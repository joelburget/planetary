{-# language LambdaCase #-}
module Interplanetary.Eval where

import Bound
import Control.Lens hiding ((??))
import Control.Monad.Except
import Control.Monad.State.Lazy
import Data.HashSet (HashSet)
import qualified Data.HashSet as HashSet
import Data.Monoid

import Interplanetary.Syntax (Uid, Row, Spine, Polytype(..), ValTy(..), CompTy(..), AdjustmentHandlers(..), Adjustment, Tm)
import qualified Interplanetary.Syntax as S
import Interplanetary.Util

data Err
  = RowBound

-- deriving instance Show Err

data Value a
  -- use values
  = Variable a
  | InstantiatePolyVar (Vector PolytypeI)
  | Command Uid Row
  | Annotation (Value a) ValTyI

  -- construction values
  | Construct Uid Row (Vector (Value a))
  | Lambda (Scope Int (Tm Int) a)

-- isValue :: Tm a b -> Bool
-- isValue = \case
--   -- Uses: all but Application
--   Variable{}           -> True
--   InstantiatePolyVar{} -> True
--   Command{}            -> True
--   Annotation{}         -> True
--
--   -- Constructions:
--   ConstructUse u       -> isValue u
--   Construct{}          -> True
--   Lambda{}             -> True
--   _                    -> False

-- type EvalContext = EitherT Err (Reader ())

-- runContext :: () -> EvalContext TmI -> Either Err TmI
-- runContext store ctxTm = runReader (runEitherT ctxTm) store

--

type EVHOLE = EvaluationContext
type UseI = Tm Int Int
type ConstructionI = Tm Int Int
type CValI = Value Int
type ValueI = Value Int
type PolytypeI = Polytype Int
type ValTyI = ValTy Int
type AdjustmentHandlersI = AdjustmentHandlers Int Int
type AdjustmentI = Adjustment Int
type TmI = Tm Int Int
type SpineI = Spine Int Int
type ConstructionValueI = Value Int

data EvaluationContext a
  = HaltK
  | OperatorK a SpineI
  | ApplicationSpineK UseI (Vector CValI) a (Vector ConstructionI)
  | AnnotationK a ValTyI
  | ConstructK Uid Row (Vector CValI) a (Vector ConstructionI)
  | CaseK a (Vector (Scope Int (Tm Int) Int))
  | HandleK AdjustmentI a AdjustmentHandlersI (Scope () (Tm Int) Int)
  | LetK PolytypeI a (Scope () (Tm Int) Int)
  deriving Functor

newtype Fix f = Fix (f (Fix f))

type EvaluationContext' = Fix EvaluationContext

handledCommands :: EvaluationContext' -> HashSet (Int, Int)
handledCommands (Fix f) = case f of
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

fillContext :: EvaluationContext () -> ValueI -> ValueI
fillContext HaltK val = val
fillContext (OperatorK () spine) _val = todo "XXX"
fillContext (ApplicationSpineK _ _ _ _) _val = todo "XXX"
fillContext (AnnotationK () ty) val = Annotation val ty
fillContext (ConstructK uid row vals () cs) val = todo "fillContext"

-- step :: (EvaluationContext, ValueI)
--      -> (EvaluationContext, ValueI)
-- step (context, focus) = case context of
--   -- ApplicationSpineK
--   CaseK hole conts -> todo "case focus"
--     -- case focus of
--     -- Construct uid row applicands -> case conts ^? ix row of
--     --   Just body -> pure $ (hole, instantiate (applicands !!) body)
--     --   Nothing -> throwError RowBound
--     -- _ -> todo "foo"

--   HandleK _adj scrutinee _handlers fallthrough ->
--     (scrutinee, instantiate1 scrutinee fallthrough)
--   HandleK _adj scrutinee (AdjustmentHandlers handlers) fallthrough ->
--     todo "evaluate handle"
--   LetK (Polytype _pBinders pVal) rhs body -> todo "letk"

-- TODO find appropriate fixity
(??) :: MonadError Err m => Maybe a -> Err -> m a
(Just a) ?? _  = pure a
Nothing ?? err = throwError err
