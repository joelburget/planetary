{-# language BangPatterns #-}
{-# language DataKinds #-}
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
import Data.Maybe (isNothing)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Semigroup
import Data.Text (Text)
import Data.Text.Prettyprint.Doc hiding (enclose)
import Data.Traversable (for)
import GHC.Exts (IsList(..))
import GHC.Generics
import Network.IPLD hiding ((.=), Row)
import qualified Network.IPLD as IPLD

import Planetary.Core.Syntax
import Planetary.Core.Syntax.Patterns
import Planetary.Core.UIdMap
import Planetary.Util

import Debug.Trace

data Err
  -- = RowBound
  = IndexErr
  | FailedHandlerLookup !Cid !Row
  | FailedIpldConversion
  | FailedForeignFun !Text
  | VariableLookup !Text
  | Incomplete
  | NoValue
  | BadContSpine ![TmI]
  | ZipNames ![Text] ![Cid]
  | LetrecZip ![Text] ![TmI]
  deriving (Eq, Show)

instance Pretty Err where
  pretty = pretty . show

data Logger = Logger
  { _logReturnState :: Text -> EvalState -> IO ()
  , _logIncomplete  :: EvalState -> IO ()
  , _logValue       :: TmI -> IO ()
  }

type Handler            = EvalState -> ForeignM EvalState
type Handlers           = UIdMap Cid [Handler]
type ValueStore         = UIdMap Cid IPLD.Value
newtype AmbientHandlers = AmbientHandlers { _ambientHandlers :: Handlers }
  deriving Monoid

storeOf :: [IPLD.Value] -> ValueStore
storeOf = fromList . fmap (\val -> (cidOf val, val))

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
type Env = Map Text Cid -- Stack (Bool, Vector Cid)

data BindingType
  = RecursiveBinding (Map Text TmI)
  | NonrecursiveBinding TmI
  | ContBinding Continuation
  deriving (Show, Generic)
instance IsIpld BindingType

data PureContinuationFrame = PureContinuationFrame
  { _pcCtx   :: !TmI
  , _pcEnv   :: !Env
  } deriving (Show, Generic)
instance IsIpld PureContinuationFrame

pattern PureFrame :: TmI -> Env -> PureContinuationFrame
pattern PureFrame ctx env = PureContinuationFrame ctx env

data ContHandler
  = EmptyHandler
  | Handler
    -- effect handlers
    !(UIdMap Cid (Vector (Vector Text, Text, TmI)))
    -- value handler
    !(Text, TmI)
    !Env
  deriving (Show, Generic)
instance IsIpld ContHandler

data ContinuationFrame = ContinuationFrame
  { _pureContinuation :: !(Stack PureContinuationFrame)
  , _handler          :: !ContHandler
  } deriving (Show, Generic)
instance IsIpld ContinuationFrame

newtype Continuation = Continuation { unCont :: Stack ContinuationFrame }
  deriving (Show, Generic, Monoid, Semigroup)
instance IsList Continuation where
  type Item Continuation = ContinuationFrame
  toList   = unCont
  fromList = Continuation
instance IsIpld Continuation

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
initEvalState store tm = EvalState tm Map.empty store
  (Continuation [ContinuationFrame [] EmptyHandler]) Nothing

lookupContinuation :: Env -> ValueStore -> Text -> Maybe Continuation
lookupContinuation env store name = do
  addr             <- env   ^? ix name
  ipld             <- store ^? ix addr
  ContBinding cont <- fromIpld ipld
  pure cont

setVal :: BindingType -> State ValueStore Cid
setVal val = do
  let ipld = toIpld val
      cid = valueCid ipld
  at cid ?= ipld
  pure cid

setVals :: ValueStore -> [TmI] -> ([Cid], ValueStore)
setVals store vals = runState (for vals (setVal . NonrecursiveBinding)) store

data FillContext a b = FillContext
  { _fill    :: !a
  , _context :: !b
  } deriving Show

type FillTmContext = FillContext TmI TmI

-- Helper for shiftContext. Invariant: list must contain a hole
shiftList :: TmI -> [TmI] -> Either (FillContext TmI [TmI]) [TmI]
shiftList val [Hole]        = Right [val]
shiftList val (Hole:tm:tms) = Left $ FillContext tm (val:Hole:tms)
shiftList val (tm:tms)      = case shiftList val tms of
  Left (FillContext tm' tms') -> Left (FillContext tm' (tm:tms'))
  Right vals -> Right (tm:vals)

-- shiftContext reinserts a value into a context and finds the next hole or
-- returns the completed term
shiftContext :: FillTmContext -> Either FillTmContext TmI
shiftContext (FillContext val ctx) = case ctx of
  DataConstructor uid row tms -> case shiftList val tms of
    Left (FillContext val ctx)
      -> Left $ FillContext val (DataConstructor uid row ctx)
    Right vals -> Right $ DataConstructor uid row vals
  AppN Hole spine -> Right $ AppN val spine
  Application f spine -> case spine of
    -- TODO: appending to the end of a list :(
    NormalSpine vals -> Left $ FillContext f (AppN Hole (vals <> [val]))
    MixedSpine (tm:tms) vals
      -> Left (FillContext tm (Application f (MixedSpine tms (vals <> [val]))))
  -- Application f spine -> case shiftList val spine of
  --   Left val ctx -> FillContext val (Application f ctx)
  --   Right vals   -> Application f vals
  Case Hole rows -> Right $ Case val rows
  -- Handle TODO?
  Let Hole pty name rhs -> Right $ Let val pty name rhs

findContext :: TmI -> Either FillTmContext TmI
findContext tm = case tm of
  DataConstructor _uid _row [] -> Right tm
  DataConstructor uid row (tm:tms) -> Left $
    FillContext tm (DataConstructor uid row (Hole:tms))
  AppN f spine -> Left $ FillContext f (AppN Hole spine)
  Application f (MixedSpine (tm:tms) vals) -> Left $
    FillContext tm (Application f (MixedSpine tms vals))
  Case scrutinee rows   -> Left $ FillContext scrutinee (Case Hole rows)
  Let body pty name rhs -> Left $ FillContext body (Let Hole pty name rhs)

isContextual :: TmI -> Bool
isContextual = \case
  DataConstructor{} -> True
  Application{}     -> True
  Case{}            -> True
  Let{}             -> True
  _                 -> False

enterContext :: EvalState -> EvalState
enterContext st = case findContext (st ^. evalFocus) of
  Left (FillContext tm ctx) -> st
    & evalFocus .~ tm
    & evalCont  . _head . pureContinuation
      %~ cons (PureFrame ctx (st ^. evalEnv))
  Right tm -> st & evalFocus .~ Value tm

lookupVariable :: Text -> Env -> ValueStore -> Maybe TmI
lookupVariable name env store = do
  addr    <- env ^? ix name
  ipld    <- store ^? ix addr
  binding <- fromIpld ipld
  case binding of
    NonrecursiveBinding tm -> pure tm
    RecursiveBinding tms   -> tms ^? ix name
    ContBinding cont       -> Nothing

shouldEnter :: TmI -> Maybe Continuation -> Bool
shouldEnter tm st = case tm of
  AppN Command{} _ -> isNothing st
  _ -> not (isValue tm) && isContextual tm

enclose :: Env -> TmI -> TmI
enclose env (Lambda names scope) = Closure names env scope
-- TODO think about this
enclose _env tm = tm

step :: AmbientHandlers -> EvalState -> EvalM EvalState
step ambient st@(EvalState focus env store cont mFwdCont) = case focus of
  tm | shouldEnter tm mFwdCont -> logReturnState "M-Enter" $ enterContext st

  Variable name
    | Just newFocus <- lookupVariable name env store
    -> logReturnState "variable lookup" $ st & evalFocus .~ newFocus

  Variable name
    | Just k' <- lookupContinuation env store name -> do
    let Continuation (Frame (PureFrame frameTm _ : pureCont) handler' : contK) = cont
        AppN Hole spine = frameTm
        k = Continuation (Frame pureCont handler' : contK)
    newFocus <- case spine of
      [arg] -> pure arg
      _     -> throwError (BadContSpine spine)
    logReturnState "M-AppCont" $ st
      & evalFocus .~ newFocus
      & evalCont  .~ k' <> k

  Lambda{} -> logReturnState "Make value from lambda" $
    let env = st ^. evalEnv
    in st & evalFocus %~ Value . enclose env
    -- in st & evalFocus %~ Value
  Closure{} -> logReturnState "Make value from closure" $ st
    & evalFocus %~ Value
  Command{} -> logReturnState "Make value from command" $ st
    & evalFocus %~ Value
  ForeignValue{} -> logReturnState "Make value from foreign" $ st
    & evalFocus %~ Value

  -- Tail-call the letrec
  Letrec names lambdas body -> do
    bindingNames <- Map.fromList <$> strictZip LetrecZip names (snd <$> lambdas)
    let recBinding = RecursiveBinding bindingNames
        (addr, store') = runState (setVal recBinding) store
    logReturnState "M-Letrec" $ st
      & evalFocus .~ body
      & evalStore .~ store'
      & evalEnv   %~ Map.union (Map.fromList (zip names (repeat addr)))

  Handle tm _adj _peg handlers valHandler ->
    logReturnState "M-Handle" $ st
      & evalFocus .~ tm
      & evalCont  %~ cons (Frame [] (Handler handlers valHandler env))

  AppN (Command uid row) _spine
    | Just _ <- mFwdCont
    , Just handler' <- ambient ^? ambientHandlers . ix uid . ix row
      -> do
       -- We've run out of possible handlers. In the links paper there's no
       -- rule to cover this case -- the machine gets stuck. We have one
       -- recourse -- check the ambient environment for a handler.
       (store', ret) <- runForeignM (st ^. evalStore) (handler' st)
       logReturnState "M-Op-Handle-Ambient" $ ret
         & evalStore .~ store'

  AppN (Command uid row) spine
    | Just fwdCont <- mFwdCont
    , Continuation (Frame pureCont handler : Frame pureCont' handler' : k) <- cont
    , Handler handlers _ handlerEnv <- handler
    , Just handleCmd <- handlers ^? ix uid . ix row
    -> do
      let (spineNames, kName, handlerBody) = handleCmd
          (bindVars, store') = flip runState store $ do
            kAddr      <- setVal (ContBinding fwdCont)
            spineAddrs <- traverse (setVal . NonrecursiveBinding) spine
            pure $ Map.fromList $ (kName, kAddr) : zip spineNames spineAddrs
      logReturnState "M-Op-Handle" $ st
        & evalFocus   .~ handlerBody
        & evalEnv     .~ Map.union bindVars handlerEnv
        & evalStore   .~ store'
        & evalCont    .~ Continuation (Frame (pureCont <> pureCont') handler' : k)
        & evalFwdCont .~ Nothing

  AppN Command{} spine
    | Just (Continuation fwdCont) <- mFwdCont
    , Continuation (delta : k) <- cont
    -> logReturnState "M-Op-Forward" $ st
      & evalCont    .~ Continuation k
      & evalFwdCont .~ Just (Continuation (fwdCont <> [delta]))

  Value val -> case cont of
    Continuation (Frame (PureFrame frameTm env' : pureCont) handler' : k)
      -> case shiftContext (FillContext val frameTm) of
        Left (FillContext focus' ctx) -> logReturnState "M-RetShift" $ st
          & evalFocus .~ focus'
          & evalCont  .~ Continuation
            (Frame (PureFrame ctx env' : pureCont) handler' : k)

        Right val -> case val of

          DataConstructor{} -> logReturnState "M-Ret DataConstructor" $ st
            & evalFocus   .~ Value val
            & evalCont    .~ Continuation (Frame pureCont handler' : k)

          AppN f spine -> do
            let (addrs, store') = setVals store spine
            case f of
              Closure names clEnv scope -> do
                newNames <- Map.fromList <$> strictZip ZipNames names addrs
                logReturnState "M-App (Closure)" $ st
                  & evalFocus   .~ scope
                  & evalStore   .~ store'
                  & evalCont    .~ Continuation (Frame pureCont handler' : k)
                  & evalEnv     .~ Map.union newNames clEnv
              Lambda names scope -> do
                newNames <- Map.fromList <$> strictZip ZipNames names addrs
                logReturnState "M-App (Lambda)" $ st
                  & evalFocus   .~ scope
                  & evalStore   .~ store'
                  & evalCont    .~ Continuation (Frame pureCont handler' : k)
                  -- & evalEnv     .~ Map.union newNames env'
                  & evalEnv     %~ Map.union newNames

                -- invariant: mFwdCont must be Nothing
                -- case mFwdCont of Nothing ->
              Command{} -> logReturnState "M-Op" $ st
                -- first rearrange this application so it's simpler for
                -- M-Op-Handle
                & evalFocus   .~ val
                & evalCont    .~ Continuation (Frame pureCont handler' : k)
                -- then apply the normal M-Op rule
                & evalFwdCont .~ Just (Continuation [])

              _ -> traceShowM f >> error "bad application"

          Case (DataConstructor _uid rowNum args) rows -> do
            let (addrs, store') = setVals store args
            (varNames, rowTm) <- rows ^? ix rowNum ?? IndexErr
            newNames <- Map.fromList <$> strictZip ZipNames varNames addrs
            logReturnState "M-Ret Case" $ st
              & evalFocus .~ rowTm
              & evalStore .~ store'
              & evalEnv   %~ Map.union newNames
              & evalCont  .~ Continuation (Frame pureCont handler' : k)

          Let body _pty name rhs -> do
            let (addr, store') = runState (setVal (NonrecursiveBinding body)) store
            logReturnState "M-Ret Let" $ st
              & evalFocus   .~ rhs
              & evalStore   .~ store'
              & evalEnv     .~ Map.insert name addr env'
              & evalCont    .~ Continuation (Frame pureCont handler' : k)

    -- M-RetHandler
    -- XXX what of k0?
    Continuation (Frame [] (Handler _handlers (name, valHandler) env') : k) -> do
      let (addr, store') = runState (setVal (NonrecursiveBinding val)) store
      logReturnState "M-RetHandler" $ st
        & evalFocus .~ valHandler
        & evalStore .~ store'
        & evalEnv   .~ Map.insert name addr env'
        & evalCont  .~ Continuation k

    _ -> do
      traceM "invalid continuation>"
      traceShowM cont
      traceM "<invalid continuation"
      error "invalid continuation"

  other -> do
    traceM "incomplete>"
    traceShowM st
    traceM "<incomplete"
    logIncomplete st

isFinished :: EvalState -> Bool
isFinished (EvalState Value{} _ _ (Continuation (Frame [] EmptyHandler : _k)) _) = True
isFinished _ = False

run :: AmbientHandlers -> Logger -> EvalState -> IO (Either Err TmI)
run ambient logger st@(EvalState tm _ _ _ _)
  | isFinished st = pure $ case tm of
      Value v -> Right v
      _       -> Left NoValue
  | otherwise = do
    eitherStack <- runEvalM ambient logger (step ambient st)
    case eitherStack of
      Left err     -> pure $ Left err
      Right stack' -> run ambient logger stack'
