{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
{-# language TupleSections #-}
module Planetary.Core.Eval
  ( Err(..)
  , EvalM
  , AmbientEnv(..)
  , EvalState(..)
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

  -- optics
  , ambientHandlers
  , valueStore
  , pureContinuation
  , handler
  , evalFocus
  , evalEnv
  , evalCont
  , evalFwdCont
  ) where

-- We use an abstract machine similar to the CEK-style machine of "Liberating
-- Effects with Rows and Handlers" - Hillerström, Lindley.

import Control.Arrow (left)
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

type Handler    = EvalState -> ForeignM EvalState
type Handlers   = UIdMap Cid [Handler]
type ValueStore = UIdMap Cid IPLD.Value
data AmbientEnv = AmbientEnv
  { _ambientHandlers :: Handlers
  , _valueStore      :: ValueStore
  }

-- data LocalEnv = LocalEnv
--   { _boundVars :: Stack [TmI]
--   , _handlers :: Handlers
--   }

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

data ContinuationFrame = ContinuationFrame
  { _pureContinuation :: Stack [TmI]
  -- invariant -- snd is a Handle, Case, or Application
  , _handler          :: TmI
  } deriving Show

pattern Frame :: Stack [TmI] -> TmI -> ContinuationFrame
pattern Frame c h = ContinuationFrame c h

data EvalState = EvalState
  { _evalFocus   :: TmI
  , _evalEnv     :: Stack [TmI]
  , _evalCont    :: Stack ContinuationFrame
  -- the forwarding continuation holds the succession of handlers that have
  -- failed to handle the operation.
  --
  -- This is:
  -- * Nothing: an operation is not being handled
  -- * Just stk: this stack of continuations didn't handle the operation
  , _evalFwdCont :: Maybe (Stack ContinuationFrame)
  } deriving Show

makeLenses ''AmbientEnv
makeLenses ''ContinuationFrame
makeLenses ''EvalState

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
  -> EvalM EvalState
  -> IO (Either Err EvalState, AmbientEnv)
runEvalM ambient state = runStateT (runExceptT state) ambient

-- runEval :: AmbientEnv -> TmI -> IO (Either Err TmI, AmbientEnv)
-- runEval env tm = do
--   m <- runEvalM env (pure (EvalState [tm] [] [] Nothing))
--   -- TODO: make total
--   pure $ left (\(EvalState [tm'] _ _ _) -> tm')

run :: AmbientEnv -> EvalState -> IO (Either Err TmI, AmbientEnv)
run ambient st@(EvalState tm _ _ _)
  | isValue tm = pure (Right tm, ambient)
  | otherwise = do
    (eitherStack, env') <- runEvalM ambient (step st)
    case eitherStack of
      Left err -> pure (Left err, env')
      Right stack' -> run env' stack'

handleCommand :: Cid -> Row -> [TmI] -> EvalState -> EvalM EvalState
handleCommand uid row spine st = case _evalFwdCont st of
  -- M-Op
  Nothing -> do
    traceRule "M-Op"
    pure $ st & evalFwdCont .~ Just []
    -- M-Op-Handle / M-Op-Forward
  Just fwdCont
  -- Just (ContinuationFrame pureCont (handlerEnv, handler))
    | Frame env  (Handle Hole _adj _peg handlers _valHandler) : k
      <- st ^. evalCont
    , Just (_name, handleTm) <- handlers ^? ix uid . ix row
    -- M-Op-Handle
    -> do
      traceRule "M-Op-Handle"
      -- XXX is this the right order?
      let updateEnv = todo "updateEnv" -- ((fwdCont : todo "vals") :)
          newCont = case k of
            [] -> todo "[] case"
            Frame env' cont : k' -> Frame (env <> env') cont : k'
      pure $ st
        & evalFocus .~ handleTm
        & evalEnv %~ updateEnv
        & evalCont .~ newCont
        & evalFwdCont .~ Nothing
  _ -> case st ^. evalCont of
         -- M-Op-Forward
         delta:rest -> do
           traceRule "M-Op-Forward"
           let delta:rest = st ^. evalCont
               Just alts = st ^. evalFwdCont
           pure $ st
             & evalCont .~ rest
             -- append the current continuation onto the bottom of the forwarding
             -- continuation
             & evalFwdCont ?~ (alts <> [delta])

         -- We've run out of possible handlers. In the links paper there's no
         -- rule to cover this case -- the machine gets stuck. We have one
         -- recourse -- check the ambient environment for a handler.
         [] -> do
           traceRule "M-Op-Handle-Ambient"
           ambient <- gets (^. ambientHandlers)
           handler <- (ambient ^? ix uid . ix row) ?? FailedHandlerLookup
           runForeignM $ handler st

pushBoundVars :: [TmI] -> EvalState -> EvalState
pushBoundVars defns env = env & evalEnv %~ (defns:)

step :: EvalState -> EvalM EvalState
step st@(EvalState focus env cont fwdCont) = case focus of
  -- M-App
  AppN (Lambda _names scope) spine -> do
    traceRule "M-App"
    pure $ st
      & evalFocus .~ open (spine !!) scope
      & pushBoundVars spine

  -- M-AppCont
  Application f (MixedSpine (tm:tms) vals) -> do
    traceRule "M-AppCont"
    pure $ st
      & evalFocus .~ tm
      & mkFrame (Application f (MixedSpine tms vals))

  -- XXX
  -- * handle putting evaled args back in arg pos
  -- * same with case scrutinee

  -- M-Case
  Case _uid1 (DataConstructor _uid2 rowNum args) rows -> do
    traceRule "M-Case"
    row <- rows ^? ix rowNum . _2 ?? IndexErr
    pure $ st
      -- XXX do we actually bind n args or 1 data constr?
      & evalFocus .~ open (args !!) row
      & pushBoundVars args

  Case uid tm rows -> do
    traceRule "Unnamed (Case)"
    pure $ st
      & evalFocus .~ tm
      & mkFrame (Case uid Hole rows)

  -- We replace all uses of `return V` with an `isValue` check
  val | isValue val -> case cont of
    -- M-RetTop
    --
    -- TODO: decide what to do here. Options:
    -- 1. add a terminated flag to the state
    -- 2. have an ambient handler for when execution finishes
    [] -> do
      traceRule "M-RetTop"
      pure st

    -- M-RetHandler -- invoke the value handler if there is no pure
    -- continuation in the current continuation frame but there is a
    -- handler
    Frame env' (Handle Hole _adj _peg _handlers (_name, valHandler)) : k -> do
      -- todo "M-RetHandler"
      traceRule "M-RetHandler"
      pure $ st
        & evalFocus .~ valHandler
        -- TODO:
        -- * I think we should have multiple return values
        -- * environment should map to a value in context
        & evalEnv   %~ ([val] :)
        & evalCont  .~ k

    -- M-RetCont -- bind a returned value if there is a pure continuation
    -- in the current continuation frame
    Frame env' cont : k -> do
      traceRule "M-RetCont"
      -- focus <- _newFocus cont
      -- _XXX
      pure $ st
        & evalFocus .~ focus
        & evalEnv   %~ ([val] :)
        & evalCont  .~ k

    -- TODO: again why are we making a let frame
    Frame env' (Let Hole polyty name body) : k -> do
      traceRule "Unnamed Let Frame"
      pure $ st
        & evalFocus .~ body
        & pushBoundVars [val]
        & evalCont .~ k

    Frame env' (Letrec _names _lambdas Hole) : k -> do
      traceRule "Unnamed Letrec Frame"
      pure $ st & evalFocus .~ val

  -- Handle (Command uid row) _adj _peg handlers _handleValue -> do
  --   let AdjustmentHandlers uidmap = handlers
  --   handler <- (uidmap ^? ix uid . ix row) -- >>= (??

  -- M-Handle
  Handle tm adj peg lambdas valHandler -> do
    traceRule "H-Handle"
    -- let mkHandler :: TmI -> Handler
    --     mkHandler tm args env = pure (tm, pushBoundVars env args)
    --     -- env' = env & handlers %~ ((mkHandler . snd <$$> lambdas) <>)
    --     handlers = mkHandler . snd <$$> lambdas
    pure $ st
      & evalFocus .~ tm
      & mkFrame (Handle Hole adj peg lambdas valHandler)

  -- M-Op / M-Op-Handle
  AppN (Command uid row) spine -> handleCommand uid row spine st
  Command uid row              -> handleCommand uid row []    st

  -- M-App (duplicated?)
  AppN f spine -> do
    traceRule "m-App (duplicated?)"
    pure $ st
      & evalFocus .~ f
      & mkFrame (AppN Hole spine)

  -- (val, _env) : (Handle Hole _ _ _ (_, handleValue), env) : stk
  --   | isValue val -> do
  --     pure $ (handleValue, pushBoundVars env [val]) : stk
  --   | otherwise -> error "impossible"

-- XXX why are we even making a frame here? just modify env?
  Let rhs polyty name body -> do
    traceRule "Unnamed Let frame maker"
    pure $ st
      & evalFocus .~ rhs
      & mkFrame (Let Hole polyty name body)

  Letrec names lambdas rhs -> do
    -- both the focus and lambdas close over the lambdas (use env')
    traceRule "Unnamed Letrec frame maker"
    pure $ st
      & evalFocus .~ rhs
      & mkFrame (Letrec names lambdas Hole)
      & pushBoundVars (snd <$> lambdas)

  _other -> error "incomplete"

mkFrame :: TmI -> EvalState -> EvalState
mkFrame tm st@(EvalState _focus env cont _fwd)
  = st & evalCont .~ Frame env tm : cont

-- debugging {{{

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

traceRule :: String -> EvalM ()
traceRule = traceM

-- }}}
