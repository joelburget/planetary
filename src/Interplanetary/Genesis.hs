{-# language Rank2Types #-}
{-# language PatternSynonyms #-}
{-# language TypeOperators #-}
{-# language MultiParamTypeClasses #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language DeriveFunctor #-}
{-# language DeriveFoldable #-}
{-# language DeriveTraversable #-}
{-# language StandaloneDeriving #-}
module Interplanetary.Genesis where

-- import Data.Hashable (Hashable)
import Control.Monad.Trans.Either
import Control.Unification
import Control.Unification.Types (UFailure)
import Control.Unification.IntVar (IntVar, IntBindingState, IntBindingT, runIntBindingT, evalIntBindingT)
import Data.Aeson (ToJSON, FromJSON)
import Data.Functor.Identity (Identity, runIdentity)
import Data.Text (Text)
import Data.Vector (Vector)
import qualified Data.Vector as V
import Data.Word (Word32)

todo :: String -> forall a. a
todo = error

newtype CID = CID Text deriving (Eq, Show, ToJSON, FromJSON)

type Index = Int
type Unique = IntVar
type Arity = Int

type ConcreteType = UTerm T IntVar
type TypeFailure = UFailure T IntVar
type TypeBindingState = IntBindingState T

data TCFailure
  = OccursFailure    IntVar ConcreteType
  | MismatchFailure  (T ConcreteType) (T ConcreteType)
  | OtherFailure     String

deriving instance Show TCFailure

instance Fallible T IntVar TCFailure where
  occursFailure   = OccursFailure
  mismatchFailure = MismatchFailure

type UnificationMonad = EitherT TCFailure (IntBindingT T Identity)

runUnificationMonad
  :: UnificationMonad a
  -> (Either TCFailure a, TypeBindingState)
runUnificationMonad = runIdentity . runIntBindingT . runEitherT

evalUnificationMonad :: UnificationMonad a -> Either TCFailure a
evalUnificationMonad = runIdentity . evalIntBindingT . runEitherT

data a ::: b = a ::: b deriving Show

type Toplevel = Term ::: ConcreteType

data LitTy
  = TypeLiteralText
  | TypeLiteralWord32
  deriving (Eq, Show)

data T ty
  = TypeLit LitTy
  | TypeTagged Index ty
  | TypeMultiVal (Vector ty)
  | TypeArrow (Vector ty) (Vector ty)

  -- This is different from arrow because it takes one of these types instead
  -- of all simultaneously
  | TypeCaseArrow (Vector ty) (Vector ty)
  deriving (Functor, Foldable, Traversable, Show)

pattern TypeLit' :: LitTy -> ConcreteType
pattern TypeLit' litTy = UTerm (TypeLit litTy)

pattern TypeTagged' :: Index -> ConcreteType -> ConcreteType
pattern TypeTagged' i ty = UTerm (TypeTagged i ty)

pattern TypeMultiVal' :: Vector ConcreteType -> ConcreteType
pattern TypeMultiVal' tys = UTerm (TypeMultiVal tys)

pattern TypeArrow'
  :: Vector ConcreteType -> Vector ConcreteType -> ConcreteType
pattern TypeArrow' dom codom = UTerm (TypeArrow dom codom)

pattern TypeCaseArrow'
  :: Vector ConcreteType -> Vector ConcreteType -> ConcreteType
pattern TypeCaseArrow' dom codom = UTerm (TypeCaseArrow dom codom)

instance Unifiable T where
  zipMatch (TypeLit l1) (TypeLit l2)
    = if l1 == l2 then Just (TypeLit l1) else Nothing
  zipMatch (TypeTagged i1 a) (TypeTagged i2 b)
    | i1 /= i2 = Nothing
    | otherwise = Just $ TypeTagged i1 (Right (a, b))
  zipMatch (TypeMultiVal as) (TypeMultiVal bs)
    = TypeMultiVal <$> pairWith' as bs
  zipMatch (TypeArrow dom1 codom1) (TypeArrow dom2 codom2)
    = TypeArrow <$> pairWith' dom1 dom2 <*> pairWith' codom1 codom2
  zipMatch (TypeCaseArrow dom1 codom1) (TypeCaseArrow dom2 codom2)
    = TypeCaseArrow <$> pairWith' dom1 dom2 <*> pairWith' codom1 codom2
  zipMatch _ _ = Nothing

pairWith' :: Vector a -> Vector a -> Maybe (Vector (Either a (a, a)))
pairWith' = pairWith (\l r -> Right (l, r))

pairWith :: (a -> b -> c) -> Vector a -> Vector b -> Maybe (Vector c)
pairWith f as bs
  = if V.length as == V.length bs then Just (V.zipWith f as bs) else Nothing

-- TODO could make linear with explicit duplicate / ignore

data Term
  = CutLambda Lambda (Vector Atom)
  | CutCase Case Atom
  | Return (Vector Atom)
  | Let Arity Term Term
  | Alloc (Vector HeapVal) Term
  deriving (Show)

data HeapVal
  = HeapLambda Lambda
  | HeapCase Case
  | HeapTagged Index HeapVal
  | HeapMultiVal (Vector HeapVal)
  | HeapAtom Atom
  deriving (Show)

data Lambda
  = Lambda Term
  | Oracle ConcreteType CID

deriving instance Show Lambda

newtype Case = Case (Vector Term) deriving (Show)

data Atom
  = Variable Index Index
  | Literal Literal
  | Term Term
  | HeapVal HeapVal
  deriving (Show)

data Literal
  = LiteralText Text
  | LiteralWord32 Word32
  deriving (Show, Eq)
