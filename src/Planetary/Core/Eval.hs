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
module Planetary.Core.Eval
  ( Err(..)
  , EvalM
  , ValueStore
  , AmbientHandlers(..)
  , EvalState(..)
  , ForeignM
  , Handler
  , Handlers
  , Stack
  , ContinuationFrame(..)
  , PureContinuationFrame(..)
  , Logger(..)
  , emptyStore
  , noAmbientHandlers
  , step
  , run
  , run'
  , runEvalM

  -- $optics
  , ambientHandlers
  , logReturnState
  , logIncomplete
  , pureContinuation
  , handler
  , evalFocus
  , evalEnv
  , evalStore
  , evalCont
  , evalFwdCont
  , finished
  ) where

-- We use an abstract machine similar to the CEK-style machine of "Liberating
-- Effects with Rows and Handlers" - Hillerström, Lindley.
--
-- The [STGi](https://github.com/quchen/stgi) project is a good reference.
--
-- Some exposition borrowed from *How to make a fast curry* but Simon Marlow
-- and Simon Peyton Jones.

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
newtype AmbientHandlers = AmbientHandlers { _ambientHandlers :: Handlers }
  deriving Monoid

emptyStore :: ValueStore
emptyStore = mempty

noAmbientHandlers :: AmbientHandlers
noAmbientHandlers = mempty

-- This is the monad you write FFI operations in.
-- TODO: what is a foreignm?
type ForeignM =
  ExceptT Err (
  StateT ValueStore
  IO
  )

data Logger = Logger
  { _logReturnState :: Text -> EvalState -> IO ()
  , _logIncomplete :: EvalState -> IO ()
  }

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

-- Maintain a stack of continuations to resume as we evaluate the current
-- target to a value
type EvalM =
  ReaderT (Logger, AmbientHandlers) (
  ExceptT Err
  IO
  )

data IsLetrec = IsLetrec | IsntLetrec
  deriving Show

data PureContinuationFrame
  = Administrative TmI
  | Bindings IsLetrec [TmI]
  deriving Show

data ContinuationFrame = ContinuationFrame
  { _pureContinuation :: Stack PureContinuationFrame
  -- invariant -- snd is a Handle, Case, or Application
  , _handler          :: TmI
  } deriving Show

instance Pretty ContinuationFrame where
  pretty (ContinuationFrame stk handler) = "ContinuationFrame (TODO)"

pattern Frame :: Stack PureContinuationFrame -> TmI -> ContinuationFrame
pattern Frame c h = ContinuationFrame c h

data Closure = Closure TmI (Stack [TmI])
  deriving Show

rollup :: Stack PureContinuationFrame -> Stack [TmI] -> Stack [TmI]
rollup [] env = env
rollup (Administrative _ : stk) env = rollup stk env
rollup (Bindings _ vals : stk) env = vals : rollup stk env

mkClosure :: Stack [TmI] -> TmI -> Closure
mkClosure = flip Closure

-- This is a CESK machine with the addition of a forwarding continuation and
-- finished flag.
data EvalState = EvalState
  { _evalFocus   :: TmI

  -- | The environment maps variables to ~addresses~ values
  , _evalEnv     :: Stack [Closure]

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
makeLenses ''EvalState

-- TODO: do this without casing? mmorph
runForeignM :: ValueStore -> ForeignM a -> EvalM (ValueStore, a)
runForeignM store action = do
  (val, store') <- liftIO $ runExceptT action `runStateT` store
  case val of
    Left err -> throwError err
    Right a -> pure (store', a)

runEvalM
  :: AmbientHandlers
  -> Logger
  -> EvalM EvalState
  -> IO (Either Err EvalState)
runEvalM ambient logger action
  = runExceptT (runReaderT action (logger, ambient))

-- runEval :: AmbientHandlers -> TmI -> IO (Either Err TmI)
-- runEval env tm = do
--   m <- runEvalM env (pure (EvalState [tm] [] [] Nothing))
--   -- TODO: make total
--   pure $ left (\(EvalState [tm'] _ _ _) -> tm')

run :: AmbientHandlers -> Logger -> EvalState -> IO (Either Err TmI)
run env logger st = do
  e <- run' env logger st
  -- TODO: do this with lens
  pure $ case e of
    Left err  -> Left err
    Right st' -> Right $ st' ^. evalFocus

run' :: AmbientHandlers -> Logger -> EvalState -> IO (Either Err EvalState)
run' ambient logger st@(EvalState tm _ _ _ _ done)
  | done = pure (Right st)
  | otherwise = do
    eitherStack <- runEvalM ambient logger (step st)
    case eitherStack of
      Left err     -> pure $ Left err
      Right stack' -> run' ambient logger stack'

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
      let closureEnv = case st ^. evalCont of
            Frame pureCont _ : _ -> rollup pureCont (st ^?! evalEnv . _head)
            -- TODO: make error for this
            _ -> error "invariant violation (no frames)"
          -- XXX add k at head
          updateEnv = cons (mkClosure closureEnv <$> spine)
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
           ambient       <- asks (^. _2 . ambientHandlers)
           handler       <- ambient ^? ix uid . ix row ?? FailedHandlerLookup
           (store', ret) <- runForeignM (st ^. evalStore) (handler st)
           logReturnState "M-Op-Handle-Ambient" $ ret & evalStore .~ store'

lookupVar :: EvalState -> Int -> Int -> Maybe (TmI, Maybe [TmI])
lookupVar (EvalState _ env _store [Frame pureCont _] _ _) level column =
  let
      -- reached the end of the pure continuation -- check the environment
      walk i [] = (, Nothing) <$> env ^? ix i . ix column

      -- found what we're looking for in the pure continuation
      walk 0 (Bindings isLetrec bindings : k) = do
        tm <- bindings ^? ix column
        pure $ case isLetrec of
          IsLetrec   -> (tm, Just bindings)
          IsntLetrec -> (tm, Nothing)

      walk i (Bindings{}       : k) = walk (i - 1) k
      walk i (Administrative{} : k) = walk i       k
  in walk level pureCont
  -- env ^? ix level . ix column

  -- cid     <- env ^? ix level . ix column
  -- ipldVal <- store ^? ix cid
  -- fromIpld ipldVal

step :: EvalState -> EvalM EvalState
step st@(EvalState focus env store cont fwdCont done) = case focus of
  BV level column -> case lookupVar st level column of
    Just (newFocus, Nothing) -> logReturnState "BV lookup (found non-letrec)" $ st
      & evalFocus .~ newFocus
    Just (newFocus, Just toInsert) -> logReturnState "BV lookup (found letrec)" $ st
      & evalFocus .~ newFocus
      & evalCont . _head . pureContinuation
        %~ cons (Bindings IsLetrec toInsert)
    Nothing -> throwError VariableLookup

  -- M-App
  AppN (Lambda _names scope) spine ->
    logReturnState "M-App" $ st
      & evalFocus .~ scope
      -- & evalEnv   %~ cons spine
      & evalCont . _head . pureContinuation
        %~ cons (Bindings IsntLetrec (mkClosure env <$> spine))

  -- eval fun arg
  Application f (MixedSpine (tm:tms) vals) ->
    logReturnState "eval fun arg" $ st
      & evalFocus .~ tm
      & evalCont . _head . pureContinuation
        %~ cons (Administrative (Application f (MixedSpine tms vals)))

  -- eval fun body
  AppN f spine ->
    logReturnState "eval fun body" $ st
      & evalFocus .~ f
      & evalCont . _head . pureContinuation %~ cons (Administrative (AppN Hole spine))

  -- M-Op / M-Op-Handle
  AppN (Command uid row) spine -> handleCommand uid row spine st
  Command uid row              -> handleCommand uid row []    st

  -- XXX
  -- * handle putting evaled args back in arg pos
  -- * same with case scrutinee

  -- M-Case
  Case (DataConstructor _uid rowNum args) rows -> do
    row <- rows ^? ix rowNum . _2 ?? IndexErr
    logReturnState "M-Case" $ st
      -- XXX do we actually bind n args or 1 data constr?
      -- XXX figure out env / cont story
      & evalFocus .~ row
      -- & evalEnv   %~ cons args
      & evalCont . _head . pureContinuation
        %~ cons (Bindings IsntLetrec args)

  Case tm rows ->
    logReturnState "make case pure frame" $ st
      & evalFocus .~ tm
      & evalCont . _head . pureContinuation
        %~ cons (Administrative (Case Hole rows))

  -- We replace all uses of `return V` with an `isValue` check
  val | isValue val -> case cont of
    -- M-RetTop
    --
    -- Options to signal termination:
    -- 1. a terminated flag on the state (choosing this for now)
    -- 2. an ambient handler for when execution finishes
    --
    -- TODO: mkClosure?
    []            -> logReturnState "M-RetTop" $ st & finished .~ True
    -- TODO: make k0 a value handler
    [Frame [] K0] -> logReturnState "M-RetTop" $ st & finished .~ True

    -- M-RetHandler -- invoke the value handler if there is no pure
    -- continuation in the current continuation frame but there is a
    -- handler
    Frame env' (Handle Hole _adj _peg _handlers (_name, valHandler)) : k ->
      logReturnState "M-RetHandler" $ st
        & evalFocus .~ valHandler
        -- TODO:
        -- * I think we should have multiple return values
        -- * environment should map to a value in context
        & evalEnv   %~ cons [mkClosure env' val]
        & evalCont  .~ k

    -- M-RetCont
    -- This is our issue in the "next one" example. We pop a letrec binding off
    -- the stack, changing where a bound var points to.
    Frame (Bindings _ bindings : env') handler : k ->
      let valClosure = Closure val (rollup bindings env')
      in logReturnState "M-Ret Bindings" $ st
           & evalEnv   %~ cons bindings
           & evalCont  .~ Frame env' handler : k

    Frame (Administrative (Application Hole (MixedSpine tms vals)) : env') handler : k
      -> logReturnState "M-Ret Application arg" $ st
        & evalFocus .~ Application Hole (MixedSpine tms (val:vals))
        & evalCont  .~ Frame env' handler : k

    Frame (Administrative (Application f spine) : env') handler : k
      -> logReturnState "M-Ret Application fun" $ st
        & evalFocus .~ Application val spine
        & evalCont  .~ Frame env' handler : k

    Frame (Administrative (Case Hole rows) : env') handler : k ->
      logReturnState "M-Ret Case" $ st
        & evalFocus .~ Case val rows
        & evalCont  .~ Frame env' handler : k

    f@Frame{} : k -> traceShowM f >> error "non-exhaustive"

  -- Handle (Command uid row) _adj _peg handlers _handleValue -> do
  --   let AdjustmentHandlers uidmap = handlers
  --   handler <- (uidmap ^? ix uid . ix row) -- >>= (??

  -- M-Handle
  Handle tm adj peg lambdas valHandler ->
    -- let mkHandler :: TmI -> Handler
    --     mkHandler tm args env = pure (tm, pushBoundVars env args)
    --     -- env' = env & handlers %~ ((mkHandler . snd <$$> lambdas) <>)
    --     handlers = mkHandler . snd <$$> lambdas
    logReturnState "M-Handle" $ st
      & evalFocus .~ tm
      & evalCont  %~ cons (Frame [] (Handle Hole adj peg lambdas valHandler))

  -- (val, _env) : (Handle Hole _ _ _ (_, handleValue), env) : stk
  --   | isValue val -> do
  --     pure $ (handleValue, pushBoundVars env [val]) : stk
  --   | otherwise -> error "impossible"

  Let body _polyty _name rhs -> do
    let Frame pureCont handler : k = cont
        cont' = Frame (Bindings IsntLetrec [body] : pureCont) handler : k
    logReturnState "M-Let" $ st
      & evalFocus .~ rhs
      & evalCont  .~ cont'

  Letrec names lambdas rhs ->
    -- both the focus and lambdas close over the lambdas (use env')
    logReturnState "Unnamed Letrec frame maker" $ st
      & evalFocus                           .~ rhs
      & evalCont . _head . pureContinuation
        %~ cons (Bindings IsLetrec (snd <$> lambdas))

  _other -> logIncomplete st

-- pushBoundVars :: [Cid] -> EvalState -> EvalState
-- pushBoundVars defns env = env & evalEnv %~ cons defns
