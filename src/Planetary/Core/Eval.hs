{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
module Planetary.Core.Eval where

import Bound
import Control.Lens hiding ((??))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Network.IPLD as IPLD hiding (Row)

import Planetary.Core.Syntax
import Planetary.Util

data Err
  = RowBound
  | IndexErr
  | InvariantViolation
  | Halt
  | FailedForeignFun
  | FailedIpldConversion
  deriving (Eq, Show)

type ForeignContinuations a b =
  UIdMap Cid [Spine Cid a b -> ForeignM a b (Tm Cid a b)]
type ForeignStore a b = UIdMap Cid IPLD.Value

type ForeignM a b c = ExceptT Err (State (ForeignStore a b)) c

-- TODO: do this without casing?
runForeignM :: ForeignM Int Int a -> ForeignStore Int Int -> EvalM a
runForeignM action store = case runExceptT action `evalState` store  of
  Left err -> throwError err
  Right a -> pure a

type EvalEnv = (ForeignContinuations Int Int, ForeignStore Int Int)
type EvalM = ExceptT Err (Reader EvalEnv)

runEvalM :: EvalEnv -> EvalM TmI -> Either Err TmI
runEvalM env action = runReader (runExceptT action) env

halt :: EvalM a
halt = throwError Halt

step :: TmI -> EvalM TmI
step v@(Value _) = pure v -- ?
step (Cut (Application spine) (Value (Lambda scope)))
  -- TODO: safe
  = pure $ instantiate (spine !!) scope
step (Cut (Case _uid1 rows) (Value (DataConstructor _uid2 rowNum args))) = do
  row <- rows ^? ix rowNum ?? IndexErr
  -- TODO: maybe we need to evaluate the args to a value first
  pure (instantiate (args !!) row)
step (Cut (Application spine) (Value (ForeignFun fUid row))) = do
  store <- asks (^. _2)
  handleForeignFun store fUid row spine
step (Cut (Handle _adj _peg handlers fallthrough) val) = case val of
  Value (Command uid row)
    -> handleCommand uid row [] val handlers
  val'@(Value _) -> pure $ instantiate1 val' fallthrough
  Cut (Application spine) (Value (Command uid row))
    -> handleCommand uid row spine val handlers
  _ -> throwError InvariantViolation
step (Cut (Let _polyty body) (Value rhs))
  = pure $ instantiate1 (Value rhs) body
step (Cut _ _) = throwError InvariantViolation

step Variable{}           = halt
step InstantiatePolyVar{} = halt
step Annotation{}         = halt

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

handleForeignFun :: ForeignStore Int Int -> Cid -> Row -> Spine Cid Int Int -> EvalM TmI
handleForeignFun store uid row spine = do
  cont <- asks (^? _1 . ix uid . ix row) >>= (?? FailedForeignFun)
  cont spine `runForeignM` store
