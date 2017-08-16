{-# language BangPatterns #-}
{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}
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
  , Stack
  , ContinuationFrame(..)
  , Logger(..)
  , step
  , run
  , run'
  , runEvalM

  -- $optics
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

import Control.Lens hiding ((??))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Text (Text)
import Network.IPLD hiding (Row, Value, (.=))
import qualified Network.IPLD as IPLD
import Data.Text.Prettyprint.Doc

import Planetary.Core.Syntax
import Planetary.Core.Syntax.Patterns
import Planetary.Core.UIdMap
import Planetary.Util

data Err
  = RowBound
  | IndexErr
  | FailedHandlerLookup
  | FailedIpldConversion
  | FailedForeignFun
  | VariableLookup
  deriving (Eq, Show)

instance Pretty Err where
  pretty = pretty . show

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

data Logger = Logger
  { _logReturnState :: Text -> EvalState -> IO ()
  , _logIncomplete :: EvalState -> IO ()
  }

logReturnState :: Text -> EvalState -> EvalM EvalState
logReturnState label st = do
  log <- asks _logReturnState
  liftIO $ log label st
  pure st

logIncomplete :: EvalState -> EvalM a
logIncomplete st = do
  log <- asks _logIncomplete
  liftIO $ log st
  error "incomplete"

-- Maintain a stack of continuations to resume as we evaluate the current
-- target to a value
type EvalM =
  ReaderT Logger
  (ExceptT Err
  (StateT AmbientEnv
  IO))

data ContinuationFrame = ContinuationFrame
  { _pureContinuation :: Stack [TmI]
  -- invariant -- snd is a Handle, Case, or Application
  , _handler          :: TmI
  } deriving Show

instance Pretty ContinuationFrame where
  pretty (ContinuationFrame stk handler) = "ContinuationFrame (TODO)"

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

  , _finished :: Bool
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
  -> Logger
  -> EvalM EvalState
  -> IO (Either Err EvalState, AmbientEnv)
runEvalM ambient logger action
  = runStateT (runExceptT (runReaderT action logger)) ambient

-- runEval :: AmbientEnv -> TmI -> IO (Either Err TmI, AmbientEnv)
-- runEval env tm = do
--   m <- runEvalM env (pure (EvalState [tm] [] [] Nothing))
--   -- TODO: make total
--   pure $ left (\(EvalState [tm'] _ _ _) -> tm')

run :: AmbientEnv -> Logger -> EvalState -> IO (Either Err TmI, AmbientEnv)
run env logger st = do
  (e, env') <- run' env logger st
  -- TODO: do this with lens
  pure $ case e of
    Left err  -> (Left err, env')
    Right st' -> (Right $ st' ^. evalFocus, env')

run' :: AmbientEnv -> Logger -> EvalState -> IO (Either Err EvalState, AmbientEnv)
run' ambient logger st@(EvalState tm _ _ _ done)
  | done = pure (Right st, ambient)
  | otherwise = do
    (eitherStack, env') <- runEvalM ambient logger (step st)
    case eitherStack of
      Left err     -> pure (Left err, env')
      Right stack' -> run' env' logger stack'

handleCommand :: Cid -> Row -> [TmI] -> EvalState -> EvalM EvalState
handleCommand uid row spine st = case _evalFwdCont st of
  -- M-Op
  Nothing -> logReturnState "M-Op" $ st & evalFwdCont .~ Just []

  -- M-Op-Handle / M-Op-Forward
  Just fwdCont
  -- Just (ContinuationFrame pureCont (handlerEnv, handler))
    | Frame env  (Handle Hole _adj _peg handlers _valHandler) : k
      <- st ^. evalCont
    , Just (_names, _kName, handleTm) <- handlers ^? ix uid . ix row
    -- M-Op-Handle
    --
    -- Use the current handler to handle an operation.
    -> do
      -- XXX is this the right order?
      let updateEnv = todo "updateEnv" -- ((fwdCont : todo "vals") :)
          newCont = case k of
            [] -> [] -- TODO is this right?
            Frame env' cont : k' -> Frame (env <> env') cont : k'
      logReturnState "M-Op-Handle" $ st
        & evalFocus   .~ handleTm
        & evalEnv     %~ updateEnv
        & evalCont    .~ newCont
        & evalFwdCont .~ Nothing
  _ -> case st ^. evalCont of
         -- M-Op-Forward
         delta:rest -> do
           let delta:rest = st ^. evalCont
               Just alts = st ^. evalFwdCont
           logReturnState "M-Op-Forward" $ st
             & evalCont .~ rest
             -- append the current continuation onto the bottom of the forwarding
             -- continuation
             & evalFwdCont ?~ (alts <> [delta])

         -- We've run out of possible handlers. In the links paper there's no
         -- rule to cover this case -- the machine gets stuck. We have one
         -- recourse -- check the ambient environment for a handler.
         [] -> do
           ambient <- gets (^. ambientHandlers)
           handler <- ambient ^? ix uid . ix row ?? FailedHandlerLookup
           ret <- runForeignM $ handler st
           logReturnState "M-Op-Handle-Ambient" ret

pushBoundVars :: [TmI] -> EvalState -> EvalState
pushBoundVars defns env = env & evalEnv %~ (defns:)

step :: EvalState -> EvalM EvalState
step st@(EvalState focus env cont fwdCont done) = case focus of
  BV level column -> case env ^? ix level . ix column of
    Just newFocus -> logReturnState "BV lookup" $ st
      & evalFocus .~ newFocus
    Nothing -> throwError VariableLookup

  -- M-App
  AppN (Lambda _names scope) spine ->
    logReturnState "M-App" $ st
      & evalFocus .~ open (spine !!) scope
      & pushBoundVars spine

  -- M-AppCont
  Application f (MixedSpine (tm:tms) vals) ->
    logReturnState "M-AppCont" $ st
      & evalFocus .~ tm
      & mkFrame (Application f (MixedSpine tms vals))

  -- XXX
  -- * handle putting evaled args back in arg pos
  -- * same with case scrutinee

  -- M-Case
  Case (DataConstructor _uid rowNum args) rows -> do
    row <- rows ^? ix rowNum . _2 ?? IndexErr
    logReturnState "M-Case" $ st
      -- XXX do we actually bind n args or 1 data constr?
      & evalFocus .~ open (args !!) row
      & pushBoundVars args

  Case tm rows ->
    logReturnState "Unnamed (Case)" $ st
      & evalFocus .~ tm
      & mkFrame (Case Hole rows)

  -- We replace all uses of `return V` with an `isValue` check
  val | isValue val -> case cont of
    -- M-RetTop
    --
    -- Options to signal termination:
    -- 1. a terminated flag on the state (choosing this for now)
    -- 2. an ambient handler for when execution finishes
    [] -> logReturnState "M-RetTop" $ st & finished .~ True

    -- M-RetHandler -- invoke the value handler if there is no pure
    -- continuation in the current continuation frame but there is a
    -- handler
    Frame env' (Handle Hole _adj _peg _handlers (_name, valHandler)) : k ->
      logReturnState "M-RetHandler" $ st
        & evalFocus .~ valHandler
        -- TODO:
        -- * I think we should have multiple return values
        -- * environment should map to a value in context
        & evalEnv   %~ ([val] :)
        & evalCont  .~ k

    Frame env' (Application f (MixedSpine tms vals)) : k
      | f /= Hole -> logReturnState "M-Ret Application 1" $ st
        & evalFocus .~ Application f (MixedSpine tms (val:vals))
        & evalCont  .~ k

    Frame env' (Application f spine) : k
      | f == Hole -> logReturnState "M-Ret Application 2" $ st
        & evalFocus .~ Application val spine
        & evalCont  .~ k

    -- M-RetCont -- bind a returned value if there is a pure continuation
    -- in the current continuation frame
    Frame env' cont : k ->
      -- focus <- _newFocus cont
      -- _XXX
      logReturnState "M-RetCont" $ st
        & evalFocus .~ cont
        & evalEnv   %~ ([val] :)
        & evalCont  .~ k

  -- Handle (Command uid row) _adj _peg handlers _handleValue -> do
  --   let AdjustmentHandlers uidmap = handlers
  --   handler <- (uidmap ^? ix uid . ix row) -- >>= (??

  -- M-Handle
  Handle tm adj peg lambdas valHandler ->
    -- let mkHandler :: TmI -> Handler
    --     mkHandler tm args env = pure (tm, pushBoundVars env args)
    --     -- env' = env & handlers %~ ((mkHandler . snd <$$> lambdas) <>)
    --     handlers = mkHandler . snd <$$> lambdas
    logReturnState "H-Handle" $ st
      & evalFocus .~ tm
      & mkFrame (Handle Hole adj peg lambdas valHandler)

  -- M-Op / M-Op-Handle
  AppN (Command uid row) spine -> handleCommand uid row spine st
  Command uid row              -> handleCommand uid row []    st

  -- M-App (duplicated?)
  AppN f spine ->
    logReturnState "M-App (duplicated?)" $ st
      & evalFocus .~ f
      & mkFrame (AppN Hole spine)

  -- (val, _env) : (Handle Hole _ _ _ (_, handleValue), env) : stk
  --   | isValue val -> do
  --     pure $ (handleValue, pushBoundVars env [val]) : stk
  --   | otherwise -> error "impossible"

  Let body polyty name rhs ->
    logReturnState "Unnamed Let frame maker" $ st
      & evalFocus .~ rhs
      & evalEnv %~ ([body] :)

  Letrec names lambdas rhs ->
    -- both the focus and lambdas close over the lambdas (use env')
    logReturnState "Unnamed Letrec frame maker" $ st
      & evalFocus .~ rhs
      & pushBoundVars (snd <$> lambdas)

  _other -> logIncomplete st

mkFrame :: TmI -> EvalState -> EvalState
mkFrame tm st@(EvalState _focus env cont _fwd _done)
  = st & evalCont .~ Frame env tm : cont
