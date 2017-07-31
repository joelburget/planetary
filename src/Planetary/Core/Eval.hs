{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
{-# language TupleSections #-}
module Planetary.Core.Eval
  ( Err(..)
  , EvalM
  , AmbientEnv(..)
  , LocalEnv(..)
  , ForeignM
  , Handler
  , Handlers
  , step
  , run
  , runEvalM

  -- debugging
  , showStack
  , showEnv
  , traceStack
  , traceStackM
  , traceEnvM
  ) where

-- We use an abstract machine similar to the CEK-style machine of "Liberating
-- Effects with Rows and Handlers" - Hillerström, Lindley.

import Control.Lens hiding ((??))
import Control.Monad.Except
import Control.Monad.State
import Network.IPLD hiding (Row, Value, (.=))
import qualified Network.IPLD as IPLD

import Planetary.Core.Syntax
import Planetary.Core.Syntax.Patterns
import Planetary.Core.UIdMap
import Planetary.Util

import Debug.Trace hiding (traceStack)

data Err
  = RowBound
  | IndexErr
  | FailedHandlerLookup
  | FailedIpldConversion
  | FailedForeignFun
  | VariableLookup
  deriving (Eq, Show)

type Handler    = [TmI] -> LocalEnv -> ForeignM (TmI, LocalEnv)
type Handlers   = UIdMap Cid [Handler]
type ValueStore = UIdMap Cid IPLD.Value
data AmbientEnv = AmbientEnv
  { _ambientHandlers :: Handlers
  , _valueStore      :: ValueStore
  }

data LocalEnv = LocalEnv
  { _boundVars :: Stack [TmI]
  , _handlers :: Handlers
  }

-- This is the monad you write FFI operations in.
-- TODO: what is a foreignm?
type ForeignM =
  ExceptT Err
  (StateT ValueStore
  IO)

-- Maintain a stack of continuations to resume as we evaluate the current
-- target to a value
type EvalM =
  ExceptT Err
  (StateT AmbientEnv
  IO)

makeLenses ''AmbientEnv
makeLenses ''LocalEnv

showStack :: Stack TmI -> String
showStack stk =
  let lines = show <$> stk
      indented = ("  " <>) <$> lines
      headed = "stack:" : indented <> ["end stack"]
  in unlines headed

showEnv :: Stack [TmI] -> String
showEnv env =
  let env' = ("  " <>) . show <$$> env
      env'' = flip imap env' $ \i stk ->
        show i ++ ":\n" ++ unlines stk
      headed = "env:" : env'' <> ["end env"]
  in unlines headed

traceStack :: Stack TmI -> Stack TmI
traceStack stk = trace (showStack stk) stk

traceStackM :: Stack TmI -> EvalM ()
traceStackM = traceM . showStack

traceEnvM :: Stack [TmI] -> EvalM ()
traceEnvM = traceM . showEnv

-- TODO: do this without casing? mmorph
runForeignM :: ForeignM a -> EvalM a
runForeignM action = do
  store <- gets (^. valueStore)
  (val, store') <- liftIO $ runExceptT action `runStateT` store
  valueStore .= store'
  case val of
    Left err -> throwError err
    Right a -> pure a

runEvalM
  :: AmbientEnv
  -> EvalM (Stack (TmI, LocalEnv))
  -> IO (Either Err (Stack (TmI, LocalEnv)), AmbientEnv)
runEvalM ambient state = runStateT (runExceptT state) ambient

run :: AmbientEnv -> Stack (TmI, LocalEnv) -> IO (Either Err TmI, AmbientEnv)
run ambient stack
  | [(tm, _env)] <- stack
  , isValue tm = pure (Right tm, ambient)
  | otherwise = do
    (eitherStack, env') <- runEvalM ambient (step stack)
    case eitherStack of
      Left err -> pure (Left err, env')
      Right stack' -> run env' stack'

-- Walk up the stack until we locate a handler for this Cid. Return the current
-- continuation and rest of the stack.
findHandler
  :: Cid
  -> Row
  -> LocalEnv

  -- args, environment they live in
  -> EvalM Handler

findHandler cid row env = case env ^? handlers . ix cid . ix row of
  Just handler -> pure handler
  Nothing -> gets (^? ambientHandlers . ix cid . ix row)
    >>= (?? FailedHandlerLookup)

pushBoundVars :: LocalEnv -> [TmI] -> LocalEnv
pushBoundVars env defns = env & boundVars %~ (defns:)

step :: Stack (TmI, LocalEnv) -> EvalM (Stack (TmI, LocalEnv))
-- step [x] | isValue x = pure [x] -- XXX should this even be a rule? Halt?
step ((BoundVariable level col, env) : stk) = do
  -- traceM $ "looking up variable " ++ show (level, col)
  -- traceM "variable env"
  -- traceEnvM $ env ^. boundVars
  -- traceM "variable stk"
  -- traceStackM $ fst <$> stk
  val <- env ^? boundVars . ix level . ix col ?? VariableLookup
  -- traceM $ "variable lookup returned: " ++ show val
  pure $ (val, env) : stk
step ((Application f (MixedSpine (tm:tms) vals), env) : stk) =
  pure $ (tm, env) : (Application f (MixedSpine tms vals), env) : stk
step ((val, _env) : (AppN Hole vals, env) : stk)
  | isValue val
  = pure $ (AppN val vals, env) : stk
step ((val, _env) : (Application f (MixedSpine tms vals), env) : stk)
  | isValue val
  = pure $ (Application f (MixedSpine tms (val:vals)), env) : stk
step ((AppN (Lambda _names scope) spine, env) : stk) = do
  traceM $ "lambda pushing spine: " ++ show spine
  pure $ (scope, pushBoundVars env spine) : stk

step ((Case _uid1 (DataConstructor _uid2 rowNum args) rows, env) : stk) = do
  row <- rows ^? ix rowNum . _2 ?? IndexErr
  pure $ (row, pushBoundVars env args) : stk

step ((Case uid tm rows, env) : stk)
  = pure $ (tm, env) : (Case uid Hole rows, env) : stk

step ((val, _env) : (Case uid Hole rows, env) : stk)
  | isValue val
  = pure $ (Case uid val rows, env) : stk

-- step (Handle (Command uid row) _adj _peg handlers _handleValue) = do
--   let AdjustmentHandlers uidmap = handlers
--   handler <- (uidmap ^? ix uid . ix row) -- >>= (??

step ((Handle tm adj peg lambdas valHandler, env) : stk) = do
  let mkHandler :: TmI -> Handler
      mkHandler tm args env = pure (tm, pushBoundVars env args)
      env' = env & handlers %~ ((mkHandler . snd <$$> lambdas) <>)
      stk' = (tm, env') : stk
  pure stk'

step ((AppN (Command uid row) spine, env) : stk) = do
  handler <- findHandler uid row env
  traceM "found handler"
  val <- runForeignM (handler spine env)
  traceM $ "handler result: " ++ show (fst val)
  traceStackM (fst <$> stk)
  pure $ val : stk

step ((Command uid row, env) : stk) = do
  handler <- findHandler uid row env
  traceM "found handler"
  val <- runForeignM (handler [] env)
  traceM $ "handler result: " ++ show (fst val)
  traceStackM (fst <$> stk)
  pure $ val : stk

-- TODO: just `f, spine : env`?
step ((AppN f spine, env) : stk)
  = pure $ (f, env) : (AppN Hole spine, env) : stk

-- step ((val, _env) : (Handle Hole _ _ _ (_, handleValue), env) : stk)
--   | isValue val = do
--     pure $ (handleValue, pushBoundVars env [val]) : stk
--   | otherwise = error "impossible"

step ((Let rhs polyty name body, env) : stk)
  = pure $ (rhs, env) : (Let Hole polyty name body, env) : stk
step ((v, _env) : (Let Hole polyty name body, env) : stk)
  | isValue v
  = pure $ (body, pushBoundVars env [v]) : stk

step ((Letrec names lambdas rhs, env) : stk) =
  let lambdaVars = snd <$> lambdas
      env' = pushBoundVars env lambdaVars

  -- both the focus and lambdas close over the lambdas (use env')
  in pure $ (rhs, env') : (Letrec names lambdas Hole, env') : stk

step ((v, env) : (Letrec _names _lambdas Hole, _env) : stk)
  | isValue v
  = pure $ (v, env) : stk

step other = traceStackM (fst <$> other) >> error "incomplete"
