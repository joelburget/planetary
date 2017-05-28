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
import Planetary.Core.Syntax.Patterns
import Planetary.Core.UIdMap
import Planetary.Util

data Err
  = RowBound
  | IndexErr
  | Halt
  | FailedHandlerLookup
  | FailedIpldConversion
  | FailedForeignFun
  | CantCut CI TmI
  deriving (Eq, Show)

type CI = ContinuationI

type CurrentHandlers a b =
  UIdMap Cid [Spine Cid a b -> ForeignM a b (Tm Cid a b)]
type HandlerStore a b = UIdMap Cid IPLD.Value
type EvalEnv = (CurrentHandlers Int Int, HandlerStore Int Int)

-- TODO: what is a foreignm?
type ForeignM a b c = ExceptT Err (State (HandlerStore a b)) c

-- Maintain a stack of continuations to resume as we evaluate the current
-- target to a value
type EvalM = ExceptT Err (StateT (Stack CI) (Reader EvalEnv))

-- TODO: do this without casing?
-- TODO: bring back runForeignM
runHandler :: Cid -> Row -> Spine Cid Int Int -> EvalM TmI
runHandler cid row spine = do
  cont <- asks (^? _1 . ix cid . ix row) >>= (?? FailedHandlerLookup)
  store <- asks (^. _2)
  let action = cont spine
  case runExceptT action `evalState` store of
    Left err -> throwError err
    Right a -> pure a

runEvalM :: EvalEnv -> Stack CI -> EvalM TmI -> (Either Err TmI, Stack CI)
runEvalM env stack action = runReader (runStateT (runExceptT action) stack) env

halt :: EvalM a
halt = throwError Halt

step :: TmI -> EvalM TmI
step (CommandV uid row tms) = do
  -- handler <- findHandler
  runHandler uid row tms
  -- handleCommand cid row spine handlers
step v@(Value _) = pure v -- ?
step Cut {cont, target} = stepCut cont target
  -- case target of
  --   Value v -> stepCut cont v
  --   _other -> do
  --     modify (cont:)
  --     pure target
step Variable{}           = halt
step InstantiatePolyVar{} = halt
step Annotation{}         = halt
step Letrec{} = todo "step letrec"

stepCut :: CI -> TmI -> EvalM TmI
stepCut (Application spine) (LambdaV _names scope)
  -- TODO: safe
  = pure $ instantiate (spine !!) scope
stepCut (Case _uid1 rows) (DataConstructorV _uid2 rowNum args) = do
  (_, row) <- rows ^? ix rowNum ?? IndexErr
  -- TODO: maybe we need to evaluate the args to a value first
  pure (instantiate (args !!) row)
stepCut (Handle _adj _peg _handlers handleValue) v@Value{} =
  pure $ instantiate1 v handleValue

stepCut (Let _polyty _name body) rhs@Value{} = pure $ instantiate1 rhs body
stepCut cont target = throwError (CantCut cont target)

-- withHandlers :: AdjustmentHandlersI -> Scope () (Tm Cid Int) Int -> EvalM a -> EvalM a
-- withHandlers (AdjustmentHandlers handlers) handleValue action $ do

handleCommand
  :: Cid
  -> Row
  -> SpineI
  -- -> TmI
  -> AdjustmentHandlersI
  -> EvalM TmI
handleCommand uid row spine (AdjustmentHandlers (UIdMap handlers)) = do
  -- look up n_c (handler)
  -- TODO this should actually just fall through not error
  handlers' <- handlers  ^? ix uid ?? IndexErr
  handler   <- handlers' ^? ix row ?? IndexErr

  let instantiator = \case
        Nothing -> LambdaV (todo "XXX") (todo "command instantiator")
        Just i -> spine !! i
  -- \case
  --       -- XXX really not sure this is right
  --       Nothing -> Value (Lambda (abstract Just val))
  --       Just i -> spine !! i

  pure (instantiate instantiator handler)
