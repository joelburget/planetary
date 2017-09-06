{-# language BangPatterns #-}
{-# language DataKinds #-}
{-# language DeriveAnyClass #-}
{-# language DeriveGeneric #-}
{-# language FlexibleContexts #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
{-# language TupleSections #-}
module Planetary.Core.Eval where

import Control.Lens hiding ((??))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Semigroup
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Traversable (for)
import GHC.Exts (IsList)
import GHC.Generics
import Network.IPLD hiding ((.=))
import qualified Network.IPLD as IPLD

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
  | NoValue Text
  | Incomplete
  deriving (Eq, Show)

instance Pretty Err where
  pretty = pretty . show

data Logger = Logger
  { _logReturnState :: Text -> EvalState -> IO ()
  , _logIncomplete :: EvalState -> IO ()
  , _logValue :: TmI -> IO ()
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

-- We use an either because each variable can point to either a heap value or a
-- continuation.
type Env = Stack (Bool, Vector Cid)

data PureFrameType
  = LetFrame
  | CaseFrame
  | AppFrame
  deriving (Show, Generic, IsIpld)

data PureContinuationFrame = PureContinuationFrame
  { _pcType  :: !PureFrameType
  , _pcTm    :: !TmI
  , _pcTerms :: !(Vector TmI)
  , _pcVals  :: !(Vector TmI)
  , _pcEnv   :: !Env
  } deriving (Show, Generic, IsIpld)

-- We only use the spine for applications, no? Could also use for multi-lets.
pattern PureFrame
  :: PureFrameType -> TmI -> [TmI] -> [TmI] -> Env -> PureContinuationFrame
pattern PureFrame frameType body tms vals env
  = PureContinuationFrame frameType body tms vals env

data ContHandler
  = K0
  | Handler !(UIdMap Cid (Vector TmI)) !TmI !Env
  deriving (Show, Generic, IsIpld)

data ContinuationFrame = ContinuationFrame
  { _pureContinuation :: !(Stack PureContinuationFrame)
  , _handler          :: !ContHandler
  } deriving (Show, Generic, IsIpld)

newtype Continuation = Continuation { unCont :: Stack ContinuationFrame }
  deriving (Show, Generic, IsIpld, Monoid, Semigroup, IsList)

type instance Index Continuation = Int
type instance IxValue Continuation = ContinuationFrame
instance Ixed Continuation where
  ix k f (Continuation lst) = Continuation <$> ix k f lst
  {-# INLINE ix #-}
instance Cons Continuation Continuation ContinuationFrame ContinuationFrame where
  _Cons = prism'
    (\(frame, Continuation frames) -> Continuation (frame:frames))
    (\case
      Continuation [] -> Nothing
      Continuation (frame:frames) -> Just (frame, Continuation frames)
    )
  {-# INLINE _Cons #-}

instance Pretty ContinuationFrame where
  pretty (ContinuationFrame _stk _handler) = "ContinuationFrame (TODO)"

pattern Frame
  :: Stack PureContinuationFrame
  -> ContHandler
  -> ContinuationFrame
pattern Frame c h = ContinuationFrame c h

-- Invariant: all values
-- data EnvRow
--   = RecRow !(Vector TmI) !(Stack EnvRow)
--   | Row    !(Vector TmI)
--   deriving Show

-- This is a CESK machine with the addition of a forwarding continuation and
-- finished flag.
data EvalState = EvalState
  { _evalFocus   :: !TmI

  -- | The environment maps variables to ~addresses~ values
  , _evalEnv     :: !Env

  -- | The store / heap / memory maps addresses to values.
  , _evalStore   :: !ValueStore

  -- | The stack is a stack of continuations saying what to do when the current
  -- expression is evaluated. CEK terminology: *the continuation*.
  , _evalCont    :: !Continuation

  -- | the forwarding continuation holds the succession of handlers that have
  -- failed to handle the operation.
  --
  -- This is:
  -- * Nothing: an operation is not being handled
  -- * Just stk: this stack of continuations didn't handle the operation
  , _evalFwdCont :: !(Maybe Continuation)

  , _isReturning :: !Bool

  -- TODO: setting finished to the final value is a gross hack
  , _finished    :: !Bool
  } deriving Show

makeLenses ''AmbientHandlers
makeLenses ''ContinuationFrame
makeLenses ''PureContinuationFrame
makeLenses ''EvalState

instance Eq PureContinuationFrame where
  -- normalize terms before comparing them
  _ == _ = todo "Eq PureContinuationFrame"
deriving instance Eq ContinuationFrame
deriving instance Eq ContHandler

emptyStore :: ValueStore
emptyStore = mempty

noAmbientHandlers :: AmbientHandlers
noAmbientHandlers = mempty

logReturnState :: Text -> EvalState -> EvalM EvalState
logReturnState label st = do
  log' <- asks (_logReturnState . fst)
  liftIO $ log' label st
  pure st

logIncomplete :: EvalState -> EvalM a
logIncomplete st = do
  log' <- asks (_logIncomplete . fst)
  liftIO $ log' st
  throwError Incomplete

logValue :: TmI -> EvalM ()
logValue val = do
  log' <- asks (_logValue . fst)
  liftIO $ log' val

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
  = EvalState tm [] store (Continuation [ContinuationFrame [] K0]) Nothing False False

lookupContinuation :: Env -> ValueStore -> Int -> Int -> Maybe Continuation
lookupContinuation env store row col = do
  (False, addrs)   <- env ^? ix row
  addr             <- addrs ^? ix col
  ipld             <- store ^? ix addr
  fromIpld ipld

valueInterpretation :: Env -> ValueStore -> TmI -> Maybe TmI
valueInterpretation env store = \case
  DataConstructor uid row args -> DataConstructor uid row
    <$> traverse (valueInterpretation env store) args
  v@ForeignValue{} -> Just v
  -- Lambda _names scope -> Just $ Closure env scope
  BoundVariable row col -> do
    (isRec, addrs) <- env   ^? ix row
    addr           <- addrs ^? ix col
    ipld           <- store ^? ix addr
    val            <- fromIpld ipld
    -- Use this to add an extra row of binders only in the letrec case
    let addRec someEnv = if isRec then (True, addrs) : someEnv else someEnv
    case val of
      Closure env' body  -> valueInterpretation (addRec env') store body
      Lambda _names body -> Just $ Closure (addRec env) body
      _                  -> Just val
  Lambda _names scope -> Just $ Closure env scope

  -- Value v -> Just v

  -- TODO: should these be translated to values?
  -- InstantiatePolyVar tm ty -> flip InstantiatePolyVar ty
  --   <$> valueInterpretation env tm
  -- Command{} -> Just tm
  -- Annotation tm ty -> flip Annotation ty <$> valueInterpretation env tm

  _ -> Nothing

setVal :: IsIpld a => a -> State ValueStore Cid
setVal val = do
  let ipld = toIpld val
      cid = valueCid ipld
  at cid ?= ipld
  pure cid

setVals :: ValueStore -> [TmI] -> ([Cid], ValueStore)
setVals store vals = runState (for vals setVal) store

step :: EvalState -> EvalM EvalState
step st@(EvalState focus env store cont mFwdCont returning done)
  = case focus of
  -- TODO is this rule necessary?
  _ | done -> error "stepping done eval state" -- pure st

  -- M-Arg
  Application f (MixedSpine (tm:tms) vals) ->
    logReturnState "M-Arg" $ st
      & evalFocus .~ tm
      & evalCont  . _head . pureContinuation
        %~ cons (PureFrame AppFrame f tms vals env)

  -- TODO: awkward: we treat this special case differently
  Application f (MixedSpine [] vals) -> do
    f' <- valueInterpretation env store f ?? NoValue "Application!"
    let (addrs, store') = setVals store vals
    logReturnState "M-Arg (empty)" $ st
      & evalFocus .~ f'
      & evalEnv   %~ cons (False, addrs)
      & evalStore .~ store'

  AppN f spine
    -- applying some handler continuation k
    | BoundVariable row col <- f
    , Just k <- lookupContinuation env store row col ->
      logReturnState "M-AppCont" $ st
        & evalFocus .~ head spine -- XXX way wrong
        & evalCont  .~ k <> cont

  -- M-Op / M-Op-Handle
  AppN (Command uid row) spine -> case mFwdCont of
    Nothing -> logReturnState "M-Op" $ st & evalFwdCont .~ Just (Continuation [])

    Just fwdCont
      | Continuation (Frame _pureCont (Handler handlers _valHandler handlerEnv) : k) <- cont
      , Just handleCmd <- handlers ^? ix uid . ix row
      -> do
        spine' <- traverse (valueInterpretation env store) spine
          ?? NoValue "M-Op-Handle"
        let (addrs, store') = flip runState store $ do
              kAddr      <- setVal fwdCont
              spineAddrs <- traverse setVal spine'
              pure $ kAddr : spineAddrs
        logReturnState "M-Op-Handle" $ st
          & evalFocus .~ handleCmd
          -- XXX what's gamma'
          & evalEnv     .~ (False, {- XXX bind k -} addrs) : env
          & evalStore   .~ store'
          & evalCont    .~ Continuation k
          & evalFwdCont .~ Nothing

    Just _fwdCont
      | Continuation [_k0] <- cont
      -> do
       -- We've run out of possible handlers. In the links paper there's no
       -- rule to cover this case -- the machine gets stuck. We have one
       -- recourse -- check the ambient environment for a handler.
       ambient       <- asks (^. _2 . ambientHandlers)
       handler'      <- ambient ^? ix uid . ix row ?? FailedHandlerLookup
       (store', ret) <- runForeignM (st ^. evalStore) (handler' st)
       logReturnState "M-Op-Handle-Ambient" $ ret
         & evalStore .~ store'
         -- & evalEnv   %~ cons
         & evalFwdCont .~ Nothing

    Just (Continuation fwdCont) -> logReturnState "M-Op-Forward" $ st
      & evalCont    %~ Continuation . tail . unCont
      & evalFwdCont <>~ Just (Continuation (fwdCont <> [cont ^?! _head]))

  -- M-Case
  Case v rows -> do
    val <- valueInterpretation env store v ?? NoValue "M-Case"
    DataConstructor _uid rowNum args <- pure val
    let (addrs, store') = setVals store args
    row <- rows ^? ix rowNum . _2 ?? IndexErr
    logReturnState "M-Case" $ st
      & evalFocus .~ row
      & evalStore .~ store'
      & evalEnv   %~ cons (False, addrs)

  Let body _polyty _name rhs ->
    -- let Frame pureCont handler : k = cont
    --     cont' = Frame (Bindings IsntLetrec [body] : pureCont) handler : k
    logReturnState "M-Let" $ st
      & evalFocus .~ body
      & evalCont  . _head . pureContinuation
        %~ cons (PureFrame LetFrame rhs [] [] env)

  -- Tail-call the letrec
  Letrec _names lambdas body -> do
    let (addrs, store') = setVals store (snd <$> lambdas)
    logReturnState "M-Letrec" $ st
      & evalFocus .~ body
      & evalStore .~ store'
      & evalEnv   %~ cons (True, addrs)

  Handle tm _adj _peg handlers valHandler -> do
    let handlers'   = handlers   & traverse . traverse %~ view _3
        valHandler' = valHandler ^. _2
    logReturnState "M-Handle" $ st
      & evalFocus .~ tm
      & evalCont  %~ cons (Frame [] (Handler handlers' valHandler' env))

  Closure env' tm -> logReturnState "M-Closure" $ st
    & evalFocus .~ tm
    & evalEnv   .~ env'

  -- We replace all uses of `return V` with an `isValue` check
  val | returning -> case cont of
    -- M-RetCont
    Continuation (Frame (PureFrame frameType rhs [] frameVals env' : pureCont) handler' : k)
      -> do
      let vals = val:frameVals
      vals' <- traverse (valueInterpretation env store) vals
        ?? NoValue "M-RetCont args"
      let (addrs, store') = setVals store vals'

      let (bodyEnv, focus') = case frameType of
            LetFrame  -> ((False, addrs) : env', rhs)
            CaseFrame -> error "CaseFrame"
            AppFrame  -> case valueInterpretation env' store' rhs of
              Just (Lambda _ scope)      -> ((False, addrs) : env', scope)
              Just (Closure clEnv scope) -> ((False, addrs) : clEnv, scope)
              _other                     -> ((False, addrs) : env', rhs)

      logReturnState "M-RetCont" $ st
        & evalFocus .~ focus'
        & evalStore .~ store'
        & evalEnv   .~ bodyEnv
        & evalCont  .~ Continuation (Frame pureCont handler' : k)

    Continuation (Frame (PureFrame ty rhs (tm:tms) vals env' : pureCont) handler' : k) ->
      logReturnState "M-ArgCont" $ st
        & evalFocus .~ tm
        & evalCont  .~
          Continuation (Frame (PureFrame ty rhs tms (val:vals) env' : pureCont) handler' : k)

    -- M-RetHandler
    -- XXX what of k0?
    Continuation (Frame [] (Handler _handlers valHandler env') : k) -> do
      val' <- valueInterpretation env store val ?? NoValue "M-RetHandler"
      let (addrs, store') = setVals store [val']
      logReturnState "M-RetHandler" $ st
        & evalFocus .~ valHandler
        & evalStore .~ store'
        & evalEnv   .~ (False, addrs) : env'
        & evalCont  .~ Continuation k

    Continuation (Frame [] K0 : _k) -> do
      val' <- valueInterpretation env store val ?? NoValue "M-RetTop"
      logReturnState "M-RetTop" $ st
        & evalFocus .~ val'
        & finished  .~ True

    _ -> error "invalid continuation"

  -- HACK: handle things which are already values
  -- TODO: remove this
  val | isValue val -> do
    val' <- valueInterpretation env store val ?? NoValue "M-Hack"
    pure $ st
      & evalFocus   .~ val'
      & isReturning .~ True

  _other -> logIncomplete st

run :: AmbientHandlers -> Logger -> EvalState -> IO (Either Err TmI)
run ambient logger st@(EvalState tm _ _ _ _ _ done)
  | done = pure (Right tm)
  | otherwise = do
    eitherStack <- runEvalM ambient logger (step st)
    case eitherStack of
      Left err     -> pure $ Left err
      Right stack' -> run ambient logger stack'
