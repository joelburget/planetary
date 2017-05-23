{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}
module Planetary.Core.Eval where

import Bound
import Control.Lens hiding ((??))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Network.IPLD hiding (Row, Value)
import qualified Network.IPLD as IPLD

import Planetary.Core.Syntax
import Planetary.Core.UIdMap
import Planetary.Util

import Debug.Trace

data Err
  = RowBound
  | IndexErr
  | InvariantViolation
  | Halt
  | FailedHandlerLookup
  | FailedIpldConversion
  deriving (Eq, Show)

type ForeignContinuations a b =
  UIdMap Cid [Spine Cid a b -> ForeignM a b (Tm Cid a b)]
type HandlerStore a b = UIdMap Cid IPLD.Value

-- type ForeignM a b c = ExceptT Err (State (HandlerStore a b)) c

-- TODO: do this without casing?
runForeignM :: ForeignM Int Int a -> HandlerStore Int Int -> EvalM a
runForeignM action store = case runExceptT action `evalState` store  of
  Left err -> throwError err
  Right a -> pure a

type CI = ContinuationI

type EvalEnv = (ForeignContinuations Int Int, HandlerStore Int Int)
type EvalM = ExceptT Err (StateT (Stack CI) (Reader EvalEnv))

runEvalM :: EvalEnv -> Stack CI -> EvalM TmI -> (Either Err TmI, Stack CI)
runEvalM env stack action = runReader (runStateT (runExceptT action) stack) env

halt :: EvalM a
halt = throwError Halt

step :: TmI -> EvalM TmI
step v@(Value _) = pure v -- ?
step Cut {cont, target} =
  case target of
    Value v -> stepCut cont v
    _other -> do
      modify (cont:)
      pure target
step Variable{}           = halt
step InstantiatePolyVar{} = halt
step Annotation{}         = halt

stepCut :: CI -> ValueI -> EvalM TmI
stepCut (Application spine) (Lambda scope)
  -- TODO: safe
  = pure $ instantiate (spine !!) scope
stepCut (Case _uid1 rows) (DataConstructor _uid2 rowNum args) = do
  row <- rows ^? ix rowNum ?? IndexErr
  -- TODO: maybe we need to evaluate the args to a value first
  pure (instantiate (args !!) row)
stepCut (Application spine) (ForeignFun fUid row) = do
  store <- asks (^. _2)
  runHandler store fUid row spine
stepCut (Handle _adj _peg handlers fallthrough) target = case target of
  Command uid row
    -> handleCommand uid row [] (Value target) handlers
  _target -> pure $ instantiate1 (Value target) fallthrough
  -- Cut (Application spine) (Value (Command uid row))
  --   -> handleCommand uid row spine target handlers
  -- _ -> throwError InvariantViolation
stepCut (Let _polyty body) rhs = pure $ instantiate1 (Value rhs) body
stepCut x y = traceShowM (x, y) >> throwError InvariantViolation

handleCommand
  :: Cid
  -> Row
  -> SpineI
  -> TmI
  -> AdjustmentHandlersI
  -> EvalM TmI
handleCommand uid row spine val (AdjustmentHandlers (UIdMap handlers)) = do
  -- look up n_c (handler)
  -- TODO this should actually just fall through not error
  handlers' <- handlers  ^? ix uid ?? IndexErr
  handler   <- handlers' ^? ix row ?? IndexErr

  let inst = \case
        -- XXX really not sure this is right
        Nothing -> Value (Lambda (abstract Just val))
        Just i -> spine !! i

  pure (instantiate inst handler)

runHandler
  :: HandlerStore Int Int -> Cid -> Row -> Spine Cid Int Int -> EvalM TmI
runHandler store uid row spine = do
  cont <- asks (^? _1 . ix uid . ix row) >>= (?? FailedHandlerLookup)
  cont spine `runForeignM` store
