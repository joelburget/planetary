{-# language Rank2Types #-}
module Interplanetary.Genesis where

-- import Data.Hashable (Hashable)
import Data.Text (Text)
import Data.Vector (Vector)
import Data.Word (Word32)

todo :: String -> forall a. a
todo = error

newtype CID = CID Text deriving (Eq, Show)

type Index = Word32
type Unique = Word32
type Arity = Word32

data Toplevel = Term ::: Type
  deriving (Show, Eq)

data Type
  = TypeLiteralText
  | TypeLiteralWord32
  | TypeTagged Index Type
  | TypeMultiVal (Vector Type)
  | TypeArrow (Vector Type) (Vector Type)

  -- This is different from arrow because it takes one of these types instead
  -- of all simultaneously
  | TypeCaseArrow (Vector Type) (Vector Type)

  | TypeMetavar Unique
  deriving (Show, Eq)

-- TODO could make linear with explicit duplicate / ignore

data Term
  = CutLambda Lambda (Vector Atom)
  | CutCase Case Atom
  | Return (Vector Atom)
  | Let Arity Term Term
  | Alloc (Vector HeapVal) Term
  deriving (Show, Eq)

data HeapVal
  = HeapLambda Lambda
  | HeapCase Case
  | HeapTagged Index HeapVal
  | HeapMultiVal (Vector HeapVal)
  | HeapAtom Atom
  deriving (Show, Eq)

data Lambda
  = Lambda Term
  | Oracle Type CID
  deriving (Show, Eq)

newtype Case = Case (Vector Term) deriving (Show, Eq)

data Atom
  = Variable Index Index
  | Literal Literal
  | Term Term
  | HeapVal HeapVal
  deriving (Show, Eq)

data Literal
  = LiteralText Text
  | LiteralWord32 Word32
  deriving (Show, Eq)
