{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
module Interplanetary.Eval where

import Bound
import Control.Lens hiding ((??))
import Control.Monad.Reader
import Control.Monad.Except

import Interplanetary.Syntax
import Interplanetary.Util

data Err
  = RowBound
  | IndexErr
  | InvariantViolation
  | Halt

type EvalEnv = (DataTypeTable Int, InterfaceTable Int)
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
step (Cut (Case _uid1 rows) (Value (DataConstructor _uid2 row args))) = pure $
  -- TODO: maybe we need to evaluate the args to a value first
  instantiate (Value . (args !!)) (rows !! row)
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
  :: Uid
  -> Row
  -> SpineI
  -> TmI
  -> AdjustmentHandlersI
  -> EvalM TmI
handleCommand uid row spine val (AdjustmentHandlers (UidMap handlers)) = do
  -- look up n_c (handler)
  -- TODO this should actually just fall through not error
  handlers' <- handlers ^? ix uid ?? IndexErr
  handler <- handlers' ^? ix row ?? IndexErr

  let inst = \case
        -- XXX really not sure this is right
        Nothing -> Value (Lambda (abstract Just val))
        Just i -> spine !! i

  pure (instantiate inst handler)
