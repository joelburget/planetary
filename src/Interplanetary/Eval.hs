{-# language DataKinds #-}
{-# language GADTs #-}
{-# language LambdaCase #-}

module Interplanetary.Eval where

import Bound
import Control.Lens hiding ((??))
import Control.Lens.At (at)
import Control.Lens.Getter (view)
import Control.Monad.Reader
import Control.Monad.Trans.Either (EitherT(runEitherT), left)
import Data.Dynamic
import Data.HashMap.Lazy (HashMap)
import Data.HashSet
import Data.Word (Word32)

import Interplanetary.Syntax
import Interplanetary.Util

type TmI = Tm Int Int
type SpineI = Spine Int Int

data Halt :: * where
  Stuck :: TmI -> Halt
  -- BadDynamic :: MultiHash -> Halt
  -- MissingOracle :: MultiHash -> Halt
  -- BadVecLookup :: Word32 -> Halt
  RowBound :: Halt

deriving instance Show Halt

isValue :: Tm a b -> Bool
isValue = \case
  -- Uses: all but OperatorApplication
  Variable{}           -> True
  InstantiatePolyVar{} -> True
  Command{}            -> True
  Annotation{}         -> True

  -- Constructions:
  ConstructUse u       -> isValue u
  Construct{}          -> True
  Lambda{}             -> True
  _                    -> False

-- type EvalContext = EitherT Halt (Reader ())

-- runContext :: () -> EvalContext TmI -> Either Halt TmI
-- runContext store ctxTm = runReader (runEitherT ctxTm) store

--

type EVHOLE = EvaluationContext
type UseI = Tm Int Int
type UseI = Tm Int Int

data EvaluationContext
  = HaltK
  | OperatorK EVHOLE SpineI
  | ApplicationSpineK UseI (Vector CValI) EVHOLE (Vector Construction)
  | AnnotationK EVHOLE ValTyI
  | ConstructK Uid Row (Vector CValI) EVHOLE (Vector Construction)
  | CaseK EVHOLE (Vector (Scope Int (Tm Int) Int))
  | HandleK AdjustmentI EVHOLE AdjustmentHandlersI (Scope () (Tm Int) Int)
  | LetK PolytypeI EVHOLE (Scope () (Tm Int) Int)

handledCommands :: EvaluationContext -> HashSet (Int, Int)
handledCommands = \case
  HaltK                       -> HashSet.empty
  OperatorK ctx _             -> handledCommands ctx
  ApplicationSpineK _ _ ctx _ -> handledCommands ctx
  AnnotationK ctx _           -> handledCommands ctx
  ConstructK _ _ _ ctx _      -> handledCommands ctx
  CaseK ctx _                 -> handledCommands ctx
  HandleK _ ctx handlers _    -> handledCommands ctx <> handlerCommands handlers
  LetK _ ctx _                -> handledCommands ctx
  where handlerCommands (AdjustmentHandlers iMap) = execState
          (iforM_ iMap $ \uid ctrs ->
            iforM_ ctrs $ \ix _ -> modify (HashSet.singleton (uid, ix) <>))
          HashSet.empty

step :: TmI -> EvalContext TmI
step = \case
  OperatorApplication
    (Annotation (Lambda lBody) (SuspendedTy (CompTy domain codomain)))
    spine ->
      let spine' = zipWith Annotation spine domain
      in pure $ instantiate (spine' !!) lBody
  Case (Construct uid row applicands) rows -> do
    body <- (rows ^? ix row) ?? RowBound
    pure $ instantiate (applicands !!) body
  Handle _adj scrutinee _handlers fallthrough ->
    pure $ instantiate1 scrutinee fallthrough
  Handle _adj scrutinee (AdjustmentHandlers handlers) _fallthrough -> todo "eval handle"
  Let (Polytype _pBinders pVal) rhs body ->
    let fTy' = instantiate (todo "instantiate with what?") pVal
        body' = instantiate1 (Annotation rhs fTy') body
    in pure body'
  -- Letrec binders body -> instantiate

-- TODO find appropriate fixity
(??) :: Maybe a -> Halt -> EvalContext a
(Just a) ?? _ = pure a
Nothing ?? err = left err
