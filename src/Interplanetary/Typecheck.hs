{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedLists #-}
module Interplanetary.Typecheck where

import Control.Lens hiding (Level, Index)
import qualified Control.Lens as Lens
import Control.Monad (forM)
import Control.Monad.Error (throwError)
import Control.Monad.Gen
import Control.Monad.Reader
import Control.Monad.State
import Data.Functor (($>))
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.Monoid ((<>))
import Data.Vector (Vector, (!?), (!))
import qualified Data.Vector as V
import Data.Word (Word32)

import Interplanetary.Genesis

import Control.Exception
import Debug.Trace

newtype Level = Level Word32 deriving (Eq, Enum)

data CheckFailure
  = PosNegMismatch Type Type
  | UnificationFailure Type Type
  | SumCaseMismatch
  | UnspecifiedFailure Int
  | TagMismatch Word32 Word32
  deriving (Show, Eq)

type TypingContext =
  -- we need a source of unique identifiers
  GenT Word32
  -- we need to (statefully) solve for metavariables
  (StateT (HashMap Unique Type)
  -- we track the types of the variables (whenever we go inside a binder).
  -- these can point to metavars (which will be solved for statefully).
  --
  -- note: we do all operations at the front, indexing in by de bruijn indices
  (ReaderT [Vector Unique]
  -- so:
  -- * the State solves for *meta*variables (with mutation)
  -- * the Reader tracks the types of variables (no mutation)

  -- and we can fail at any time
  (Either CheckFailure)))

topCheck :: Toplevel -> Maybe CheckFailure
topCheck (tm ::: ty) = case runTypingContext (check tm [ty]) of
  Left fail -> Just fail
  Right () -> Nothing

runTypingContext :: TypingContext a -> Either CheckFailure a
runTypingContext m =
  let m' = runGenT m
      m'' = evalStateT m' HashMap.empty -- TODO do we need to inspect the state?
      m''' = runReaderT m'' []
  in m'''

-- TODO: there's an *awful* lot of duplication between this and solveFor
lookupType :: Index -> Index -> TypingContext (Maybe Type)
lookupType level index = do
  tys <- ask

  let i :: Word32 -> Int
      i = fromIntegral

      ident :: Maybe Unique
      ident = tys ^? ix (i level) . ix (i index)

  case ident of
    Nothing -> pure Nothing
    Just ident' -> do
      mutable <- get
      pure $ case mutable ^? ix ident' of
        Nothing              -> Nothing
        Just (TypeMetavar _) -> Nothing
        something            -> something

underBinder :: Word32 -> TypingContext a -> TypingContext a
underBinder size action = do
  -- generate `size` unique ids -- one for each variable bound at this level
  vec <- V.replicateM (fromIntegral size) gen
  local (vec:) action

generateVars :: TypingContext (Vector Type)
generateVars = do
  binderIds <- getScopeUniques
  -- Set to a metavar if not already solved
  forM binderIds $ \unique -> setDefault unique (TypeMetavar unique)

-- TODO should this be a Maybe at the top level?
getScopeUniques :: TypingContext (Vector Unique)
-- getScopeUniques = head <$> ask
getScopeUniques = do
  lst <- ask
  assert (length lst > 0) (pure (head lst))

-- Set @Just@ a value if it's currently @Nothing@.
setDefault :: (MonadState s m, At s, b ~ IxValue s) => Lens.Index s -> b -> m b
setDefault index def = do
  state <- get
  case state ^? ix index of
    Just alreadyThere -> pure alreadyThere
    Nothing -> at index <?= def

solveFor :: Level -> Index -> Type -> TypingContext ()
solveFor (Level level) index ty = do
  tys <- ask

  let i :: Word32 -> Int
      i = fromIntegral

      ident :: Maybe Unique
      ident = tys ^? ix (i level) . ix (i index)

  case ident of
    Nothing -> throwError (UnspecifiedFailure 1)
    Just ident' -> do
      mutable <- get
      case mutable ^? ix ident' of
        Nothing -> at ident' ?= ty
        Just currentSolution' -> when (currentSolution' == ty) $
          throwError (UnspecifiedFailure 2)

unify :: Type -> Type -> TypingContext Type
unify TypeLiteralText TypeLiteralText = pure TypeLiteralText
unify TypeLiteralWord32 TypeLiteralWord32 = pure TypeLiteralWord32
-- TODO we can probably simplify ty if we've just solved for a metavar
unify (TypeMetavar v) ty = (at v ?= ty) $> ty
unify ty v@(TypeMetavar _) = unify v ty
unify (TypeTagged i1 ty1) (TypeTagged i2 ty2) = do
  when (i1 /= i2) (throwError (TagMismatch i1 i2))
  unify ty1 ty2
unify (TypeMultiVal tys1) (TypeMultiVal tys2)
  = TypeMultiVal <$> unifyVec tys1 tys2
unify (TypeArrow dom1 codom1) (TypeArrow dom2 codom2)
  = TypeArrow <$> unifyVec dom1 dom2 <*> unifyVec codom1 codom2
unify ty1 ty2 = throwError (UnificationFailure ty1 ty2)

unifyVec :: Vector Type -> Vector Type -> TypingContext (Vector Type)
unifyVec tys1 tys2 = lengthChecking unify tys1 tys2

check :: Term -> Vector Type -> TypingContext ()
check (CutLambda lambda args) tys = spliceLambda lambda args tys
check (CutCase branches scrutinee) tys = spliceCase branches scrutinee tys
check (Return atoms) tys = void $ lengthChecking checkAtom atoms tys

-- to infer a let we look for the solution of its metavariable after checking
-- the rhs
check (Let arity body rhs) tys = underBinder arity $ do
  vars <- generateVars
  check body vars
  check rhs tys
check (Alloc vals rhs) tys = underBinder (len vals) $ do
  vars <- generateVars
  forM_ (V.zip vals vars) (uncurry checkHeapVal)
  check rhs tys

checkHeapVal :: HeapVal -> Type -> TypingContext ()
checkHeapVal (HeapLambda (Lambda lam)) (TypeArrow dom codom)
  -- TODO check this actually unifies dom
  = underBinder (len dom) (check lam codom)
checkHeapVal (HeapLambda _) _ = throwError (UnspecifiedFailure 3)
checkHeapVal (HeapCase (Case branches)) (TypeCaseArrow tyChoices codom) = do
  when (len branches /= len tyChoices) (throwError (UnspecifiedFailure 4))
  -- XXX we haven't specified the binder type
  forM_ (V.zip branches tyChoices) $
    \(branch, ty) -> underBinder 1 (check branch codom)
checkHeapVal (HeapCase _) _ = throwError (UnspecifiedFailure 5)
checkHeapVal (HeapTagged tag val) (TypeTagged tagBound ty) = do
  when (tag > tagBound) (throwError (UnspecifiedFailure 6))
  checkHeapVal val ty
checkHeapVal (HeapTagged tag val) ty = traceShow ty $ assert False $ throwError (UnspecifiedFailure 7)
checkHeapVal (HeapMultiVal vals) (TypeMultiVal tys) = void $
  lengthChecking checkHeapVal vals tys
checkHeapVal (HeapMultiVal _) _ = throwError (UnspecifiedFailure 8)
checkHeapVal (HeapAtom atom) ty = checkAtom atom ty

-- | Both cases are very easy
spliceLambda :: Lambda -> Vector Atom -> Vector Type -> TypingContext ()
spliceLambda lam args resultTys = underBinder (len args) $ case lam of
  -- In this case we just need to check the term saturates to the right type
  Lambda tm -> check tm resultTys
  -- And for oracles it's even easier -- we already have its type
  Oracle ty _hash -> void $ unify ty (TypeMultiVal resultTys)

-- track the metavariables in this level, error if not all solved when we exit
entangling :: Word32 -> TypingContext () -> TypingContext ()
entangling size action = underBinder size $ do
  action
  uniques <- getScopeUniques
  mapM_ checkIsSolved uniques

-- Check that this variable resolves to a complete type, with all varaibles
-- solved
checkIsSolved :: Unique -> TypingContext ()
checkIsSolved u = do
  resolution <- gets (^? ix u)
  case resolution of
    Just (TypeMetavar u') -> checkIsSolved u'
    Just _ -> pure ()
    Nothing -> throwError (UnspecifiedFailure 9)

spliceCase :: Case -> Atom -> Vector Type -> TypingContext ()
spliceCase (Case branches) scrutinee expected = do
  -- bind one branch at a time
  forM_ branches $ \branch -> do
    unique <- underBinder 1 $ do
      uniques <- getScopeUniques -- :: TypingContext (Vector Unique)
      let unique = assert (V.length uniques == 1) (V.head uniques)

      check branch expected
      pure unique

    -- now entangle the scrutinee and rhs
    checkAtom scrutinee (TypeMetavar unique)

checkAtom :: Atom -> Type -> TypingContext ()
checkAtom (Variable level ix) ty = do
  ty' <- lookupType level ix
  expect (ty' == Just ty)
checkAtom (Literal (LiteralText _)) ty = expect (ty == TypeLiteralText)
checkAtom (Literal (LiteralWord32 _)) ty = expect (ty == TypeLiteralWord32)
checkAtom (Term tm) ty = check tm [ty]
checkAtom (HeapVal val) ty = checkHeapVal val ty

lengthChecking
  :: (a -> b -> TypingContext c)
  -> Vector a
  -> Vector b
  -> TypingContext (Vector c)
lengthChecking fun vals tys = do
  when (len vals /= len tys) (throwError (UnspecifiedFailure 11))
  forM (V.zip vals tys) (uncurry fun)

expect :: Bool -> TypingContext ()
expect True = pure ()
expect False = throwError (UnspecifiedFailure 12)

len :: Vector a -> Index
len = fromIntegral . V.length
