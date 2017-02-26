{-# language LambdaCase #-}
{-# language TypeOperators #-}
module Interplanetary.Typecheck where

import Control.Lens.Indexed (iforM_)
import Control.Monad (when)
import Control.Monad.Trans (lift)
import Control.Monad.Trans.Either
import Control.Unification
import qualified Data.Vector as V
import Data.Vector (Vector)

import Interplanetary.Genesis

topCheck :: Toplevel -> Maybe TCFailure
topCheck = maybeLeft . evalUnificationMonad . check

check :: Term ::: ConcreteType -> UnificationMonad ConcreteType
check (CutLambda lam args ::: TypeArrow' argTys resultTys) = do
  when (V.length args /= V.length argTys)
    (failMessage "CutLambda mismatched args")
  typings <- zipTypings args argTys
  mapM_ checkAtom typings
  --- XXX enscope variables
  _ <- checkSaturatedLambda (lam ::: resultTys)
  pure (TypeArrow' argTys resultTys)
check (CutCase (Case branches) atom ::: resultTy) = do
  var <- getFreeVar
  atomTy <- checkAtom (atom ::: var)
  case atomTy of
    TypeTagged' ix ty -> if ix >= V.length branches
      then failMessage "case cut index out of range"
      -- XXX must enscope variable
      else check (branches V.! ix ::: resultTy)
    _ -> failMessage "non-tagged-ty in case cut"
check (Return atoms ::: TypeMultiVal' tys) = do
  zipped <- zipTypings atoms tys
  TypeMultiVal' <$> V.mapM checkAtom zipped
-- XXX arity unused
check (Let arity body rhs ::: ty) = do
  var <- getFreeVar
  bodyTy <- check (body ::: var)
  -- XXX enscope variable
  check (rhs ::: ty)
check (Alloc heapVals rhs ::: ty) = do
  vars <- V.replicateM (V.length heapVals) getFreeVar
  -- XXX enscope variables
  typings <- zipTypings heapVals vars
  mapM_ checkHeapVal typings
  -- XXX enscope variables
  check (rhs ::: ty)
check _ = failMessage "check mismatch"

checkHeapVal :: HeapVal ::: ConcreteType -> UnificationMonad ConcreteType
checkHeapVal (HeapLambda lam ::: ty@(TypeArrow' dom codom)) = do
  todo "add dom to context"
  checkSaturatedLambda (lam ::: codom)
  pure ty
checkHeapVal (HeapCase (Case branches) ::: TypeCaseArrow' options resultTys)
  = do
    branchOptions <- lengthZipWith (,) branches options
    iforM_ branchOptions $ \ix (branch, option) -> do
      case option of
        TypeTagged' tyIx ty -> do
          when (tyIx /= ix) $ failMessage "wrong order for heap case branches"
          -- XXX enscope variable
          check (branch ::: TypeMultiVal' resultTys)
        _ -> failMessage "non type-tagged option type"
    -- TODO return refined type
    pure $ TypeCaseArrow' options resultTys
checkHeapVal (HeapTagged tmIx val ::: TypeTagged' tyIx ty) = do
  when (tmIx /= tyIx) $ failMessage "tagged ty and tm with different ixes"
  TypeTagged' tyIx <$> checkHeapVal (val ::: ty)
checkHeapVal (HeapMultiVal vals ::: TypeMultiVal' tys) = do
  typings <- zipTypings vals tys
  mapM_ checkHeapVal typings
  pure $ TypeMultiVal' tys
checkHeapVal (HeapAtom atom ::: ty) = checkAtom (atom ::: ty)

checkSaturatedLambda
  :: Lambda ::: Vector ConcreteType -> UnificationMonad (Vector ConcreteType)
checkSaturatedLambda (Lambda lam ::: resultTys) = do
  TypeMultiVal' result <- check (lam ::: TypeMultiVal' resultTys)
  pure result
checkSaturatedLambda (Oracle cty _cid ::: resultTys) = todo "check Oracle"
  -- XXX how to check we saturated right number of args?

checkAtom :: Atom ::: ConcreteType -> UnificationMonad ConcreteType
checkAtom (Variable _ _ ::: ty) = todo "checkAtom variable"
checkAtom (Literal lit ::: TypeLit' ty)
  = TypeLit' <$> checkLiteral (lit ::: ty)
checkAtom (Term tm ::: ty) = check (tm ::: ty)
checkAtom (HeapVal val ::: ty) = checkHeapVal (val ::: ty)

checkLiteral :: Literal ::: LitTy -> UnificationMonad LitTy
checkLiteral (LiteralText _ ::: TypeLiteralText) = pure TypeLiteralText
checkLiteral (LiteralWord32 _ ::: TypeLiteralWord32) = pure TypeLiteralWord32
checkLiteral _ = failMessage "literal checking failure"

failMessage :: String -> UnificationMonad a
failMessage = left . OtherFailure

lengthZipWith
  :: (a -> b -> c) -> Vector a -> Vector b -> UnificationMonad (Vector c)
lengthZipWith f as bs = case pairWith f as bs of
  Just v -> pure v
  Nothing -> failMessage "lengthZipWith bad lengths"

zipTypings :: Vector a -> Vector b -> UnificationMonad (Vector (a ::: b))
zipTypings = lengthZipWith (:::)

getFreeVar :: UnificationMonad ConcreteType
getFreeVar = lift (UVar <$> freeVar)

maybeLeft :: Either a b -> Maybe a
maybeLeft = \case
  Left fail -> Just fail
  Right _ -> Nothing
