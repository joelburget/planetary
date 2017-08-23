{-# language BangPatterns #-}
{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
{-# language TupleSections #-}
module Planetary.Core.Eval where

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

import Debug.Trace

data Err
  -- = RowBound
  = IndexErr
  | FailedHandlerLookup
  | FailedIpldConversion
  | FailedForeignFun
  | VariableLookup
  | NoValue
  deriving (Eq, Show)

instance Pretty Err where
  pretty = pretty . show

data Logger = Logger
  { _logReturnState :: Text -> EvalState -> IO ()
  , _logIncomplete :: EvalState -> IO ()
  }

type Handler    = EvalState -> ForeignM EvalState
type Handlers   = UIdMap Cid [Handler]
type ValueStore = UIdMap Cid IPLD.Value
newtype AmbientHandlers = AmbientHandlers { _ambientHandlers :: Handlers }
  deriving Monoid

-- This is the monad you write FFI operations in.
type ForeignM =
  -- we can throw errors
  ExceptT Err (
  -- we do a lot of modification of values
  StateT ValueStore
  IO
  )

-- Maintain a stack of continuations to resume as we evaluate the current
-- target to a value
type EvalM =
  ReaderT (Logger, AmbientHandlers) (
  ExceptT Err
  IO
  )

data PureContinuationFrame = PureContinuationFrame
  { _tm  :: TmI
  , _env :: Stack [TmI]
  }
  deriving Show

pattern PFrame :: TmI -> Stack [TmI] -> PureContinuationFrame
pattern PFrame tm env = PureContinuationFrame tm env

data ContHandler
  = K0
  | Handler !TmI !(Stack [TmI])
  deriving Show

data ContinuationFrame = ContinuationFrame
  { _pureContinuation :: Stack PureContinuationFrame
  -- invariant -- snd is a Handle, Case, or Application
  , _handler          :: ContHandler
  } deriving Show

instance Pretty ContinuationFrame where
  pretty (ContinuationFrame stk handler) = "ContinuationFrame (TODO)"

pattern Frame
  :: Stack PureContinuationFrame -> ContHandler -> ContinuationFrame
pattern Frame c h = ContinuationFrame c h

data EnvValue
  = EnvTm !TmI
  | EnvCont !(Stack ContinuationFrame)
  deriving Show

-- This is a CESK machine with the addition of a forwarding continuation and
-- finished flag.
data EvalState = EvalState
  { _evalFocus   :: TmI

  -- | The environment maps variables to ~addresses~ values
  , _evalEnv     :: Stack [EnvValue]

  -- | The store / heap / memory maps addresses to values.
  , _evalStore   :: ValueStore

  -- | The stack is a stack of continuations saying what to do when the current
  -- expression is evaluated. CEK terminology: *the continuation*.
  , _evalCont    :: Stack ContinuationFrame

  -- | the forwarding continuation holds the succession of handlers that have
  -- failed to handle the operation.
  --
  -- This is:
  -- * Nothing: an operation is not being handled
  -- * Just stk: this stack of continuations didn't handle the operation
  , _evalFwdCont :: Maybe (Stack ContinuationFrame)

  , _finished :: Bool
  } deriving Show

makeLenses ''AmbientHandlers
makeLenses ''ContinuationFrame
makeLenses ''PureContinuationFrame
makeLenses ''EvalState

emptyStore :: ValueStore
emptyStore = mempty

noAmbientHandlers :: AmbientHandlers
noAmbientHandlers = mempty

logReturnState :: Text -> EvalState -> EvalM EvalState
logReturnState label st = do
  log <- asks (_logReturnState . fst)
  liftIO $ log label st
  pure st

logIncomplete :: EvalState -> EvalM a
logIncomplete st = do
  log <- asks (_logIncomplete . fst)
  liftIO $ log st
  error "incomplete"

runEvalM
  :: AmbientHandlers
  -> Logger
  -> EvalM EvalState
  -> IO (Either Err EvalState)
runEvalM ambient logger action
  = runExceptT (runReaderT action (logger, ambient))

-- TODO: do this without casing? mmorph
runForeignM :: ValueStore -> ForeignM a -> EvalM (ValueStore, a)
runForeignM store action = do
  (val, store') <- liftIO $ runExceptT action `runStateT` store
  case val of
    Left err -> throwError err
    Right a -> pure (store', a)

initEvalState :: ValueStore -> TmI -> EvalState
initEvalState store tm
  = EvalState tm [] store [ContinuationFrame [] K0] Nothing False

valueInterpretation :: Stack [EnvValue] -> TmI -> Maybe EnvValue
valueInterpretation env tm = case tm of
  -- TODO
  BoundVariable row col -> env ^? ix row . ix col

  _ -> Nothing

valueInterpretation' :: Stack [EnvValue] -> TmI -> Maybe TmI
valueInterpretation' env tm = case tm of
  FreeVariable{} -> Nothing
  BoundVariable row col -> case env ^? ix row . ix col of
    Just (EnvTm tm) -> Just tm
    _ -> Nothing
  DataConstructor uid row args
    -> DataConstructor uid row <$> sequence (valueInterpretation' env <$> args)
  ForeignValue{} -> Just tm
  Lambda _names scope -> Just $ Closure env scope
  InstantiatePolyVar tm ty -> flip InstantiatePolyVar ty
    <$> valueInterpretation' env tm
  Command{} -> Just tm
  Annotation tm ty -> flip Annotation ty <$> valueInterpretation' env tm

  _ -> Nothing

step :: EvalState -> EvalM EvalState
step st@(EvalState focus env store cont mFwdCont done) = case focus of
  -- TODO is this rule necessary?
  _ | done -> pure st

  -- M-App / M-AppCont
  AppN f spine -> case valueInterpretation env f of
    Just (EnvTm (Closure env' scope)) -> logReturnState "M-App" $ st
      & evalFocus .~ scope
      & evalEnv   .~ spine : env'

    -- applying some handler continuation k
    Just (EnvCont k) -> logReturnState "M-AppCont" $ st
      & evalFocus .~ head spine -- XXX way wrong
      & evalCont  .~ k <> cont

    -- M-Op / M-Op-Handle
    Just (Command uid row) -> case mFwdCont of
      Nothing -> logReturnState "M-Op" $ st & evalFwdCont .~ Just []

      Just fwdCont
        -- XXX what of k0?
        | Frame pureCont (Handler (Handle Hole _adj _peg handlers _valHandler) handleEnv) : k
          <- cont
        , Just (_names, _kName, handleCmd) <- handlers ^? ix uid . ix row
        -> do
          spine' <- sequence (valueInterpretation env <$> spine) ?? NoValue
          logReturnState "M-Op-Handle" $ st
            & evalFocus .~ handleCmd
            -- XXX what's gamma'
            & evalEnv     .~ {- XXX bind k -} spine' : env
            & evalCont    .~ k
            & evalFwdCont .~ Nothing

      Just fwdCont
        | [k0] <- cont
        -> do
         -- We've run out of possible handlers. In the links paper there's no
         -- rule to cover this case -- the machine gets stuck. We have one
         -- recourse -- check the ambient environment for a handler.
         ambient       <- asks (^. _2 . ambientHandlers)
         handler       <- ambient ^? ix uid . ix row ?? FailedHandlerLookup
         (store', ret) <- runForeignM (st ^. evalStore) (handler st)
         logReturnState "M-Op-Handle-Ambient" $ ret
           & evalStore .~ store'
           -- & evalEnv   %~ cons
           & evalFwdCont .~ Nothing

      Just fwdCont -> logReturnState "M-Op-Forward" $ st
        & evalCont    %~ tail
        & evalFwdCont . _Just <>~ [head cont]
        -- better version?
        -- & evalFwdCont . _Just %~ (|> head cont) -- (snoc)

    _ -> do
      traceShowM f
      todo "M-AppCont"

  -- M-Arg
  Application f (MixedSpine (tm:tms) vals) ->
    logReturnState "M-Arg" $ st
      & evalFocus .~ tm
      & evalCont  . _head . pureContinuation
        %~ cons (Administrative (Closure (Application f (MixedSpine tms vals)) env))

  -- M-ArgCont

  -- M-Case
  Case v rows -> do
    DataConstructor _uid rowNum args <- valueInterpretation env v ?? NoValue
    row <- rows ^? ix rowNum . _2 ?? IndexErr
    logReturnState "M-Case" $ st
      & evalFocus .~ row
      -- XXX do we actually bind n args or 1 data constr?
      & evalEnv   %~ cons args

  Let body polyty name rhs ->
    -- let Frame pureCont handler : k = cont
    --     cont' = Frame (Bindings IsntLetrec [body] : pureCont) handler : k
    logReturnState "M-Let" $ st
      & evalFocus .~ body
      & evalCont  . _head . pureContinuation
        %~ cons (PFrame (Let Hole polyty name rhs) env)

  Handle tm adj peg handlers valHandler ->
    logReturnState "M-Handle" $ st
      & evalFocus .~ tm
      & evalCont
        %~ cons (Frame [] (Handler (Handle Hole adj peg handlers valHandler) env))

  -- We replace all uses of `return V` with an `isValue` check
  val | isValue val -> case cont of
    -- M-RetCont
    Frame (PFrame (Let Hole _ _ rhs) env' : pureCont) handler : k -> do
      val' <- valueInterpretation env val ?? NoValue
      logReturnState "M-RetCont" $ st
        & evalEnv   .~ [val'] : env'
        & evalCont  .~ Frame pureCont handler : k

    -- M-RetHandler
    -- XXX what of k0?
    Frame [] (Handler (Handle Hole _ _ _handlers (_, valHandler)) env) : k -> do
      val' <- valueInterpretation env val ?? NoValue
      logReturnState "M-RetHandler" $ st
        & evalFocus .~ valHandler
        & evalEnv   %~ cons [val']
        & evalCont  .~ k

    Frame [] K0 : k -> do
      val <- valueInterpretation env val ?? NoValue
      logReturnState "M-RetTop" $ st
        & evalFocus .~ val
        & finished  .~ True

  _other -> logIncomplete st

run :: AmbientHandlers -> Logger -> EvalState -> IO (Either Err EvalState)
run ambient logger st@(EvalState tm _ _ _ _ done)
  | done = pure (Right st)
  | otherwise = do
    eitherStack <- runEvalM ambient logger (step st)
    case eitherStack of
      Left err     -> pure $ Left err
      Right stack' -> run ambient logger stack'
