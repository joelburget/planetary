{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# language OverloadedStrings #-}
{-# language TypeSynonymInstances #-}
{-# language LambdaCase #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language FlexibleInstances #-}
{-# language TypeOperators #-}

-- TODO: move to the Internal namespace
module Interplanetary.JSON where

import Data.Aeson
import Data.Aeson.Types (Parser, typeMismatch)
import Data.Scientific (toBoundedInteger)
import Data.Text (Text)
import qualified Data.Vector as V
import Data.Word (Word32)

import Interplanetary.Genesis

tj :: ToJSON a => a -> Value
tj = toJSON

fj :: FromJSON a => Value -> Parser a
fj = parseJSON

pattern Arr :: [Value] -> Value
pattern Arr lst <- (Array (V.toList -> lst)) where
  Arr lst = Array (V.fromList lst)

pattern Word :: Word32 -> Value
pattern Word i <- Number (toBoundedInteger -> Just i) where
  Word i = tj i

pattern Int :: Int -> Value
pattern Int i <- Number (toBoundedInteger -> Just i) where
  Int i = tj i

pattern ToplevelJSON :: Value -> Value -> Value
pattern ToplevelJSON tm ty = Arr ["toplevel", tm, ty]

instance ToJSON Toplevel where
  toJSON (tm ::: ty) = ToplevelJSON (tj tm) (tj ty)

instance FromJSON Toplevel where
  parseJSON = \case
    ToplevelJSON tm ty -> (:::) <$> fj tm <*> fj ty
    invalid -> typeMismatch "Toplevel" invalid

instance ToJSON LitTy where
  toJSON = \case
    TypeLiteralText -> "ty-lit-text"
    TypeLiteralWord32 -> "ty-lit-word32"

instance FromJSON LitTy where
  parseJSON = \case
    "ty-lit-text" -> pure TypeLiteralText
    "ty-lit-word32" -> pure TypeLiteralWord32
    invalid -> typeMismatch "LitTy" invalid

pattern TypeLitJSON :: Value -> Value
pattern TypeLitJSON val = Arr ["type-lit", val]

pattern TypeTaggedJSON :: Value -> Value -> Value
pattern TypeTaggedJSON i ty = Arr ["type-tagged", i, ty]

pattern TypeMultiValJSON :: Value -> Value
pattern TypeMultiValJSON tys = Arr ["type-tagged", tys]

pattern TypeArrowJSON :: Value -> Value -> Value
pattern TypeArrowJSON dom codom = Arr ["type-arrow", dom, codom]

pattern TypeCaseArrowJSON :: Value -> Value -> Value
pattern TypeCaseArrowJSON dom codom = Arr ["type-case-arrow", dom, codom]

instance ToJSON ConcreteType where
  toJSON = \case
    TypeLit' lit -> TypeLitJSON (tj lit)
    TypeTagged' ix ty -> TypeTaggedJSON (tj ix) (tj ty)
    TypeMultiVal' tys -> TypeMultiValJSON (tj tys)
    TypeArrow' dom codom -> TypeArrowJSON (tj dom) (tj codom)
    TypeCaseArrow' dom codom -> TypeCaseArrowJSON (tj dom) (tj codom)
    _ -> error "jsonifying unification var"

instance FromJSON ConcreteType where
  parseJSON = \case
    TypeLitJSON lit -> TypeLit' <$> fj lit
    TypeTaggedJSON i ty -> TypeTagged' <$> fj i <*> fj ty
    TypeMultiValJSON tys -> TypeMultiVal' <$> fj tys
    TypeArrowJSON dom codom -> TypeArrow' <$> fj dom <*> fj codom
    TypeCaseArrowJSON dom codom -> TypeCaseArrow' <$> fj dom <*> fj codom
    invalid -> typeMismatch "ConcreteType" invalid

pattern CutLambdaJSON :: Value -> Value -> Value
pattern CutLambdaJSON lam args = Arr ["cut-lambda", lam, args]

pattern CutCaseJSON :: Value -> Value -> Value
pattern CutCaseJSON cs atom = Arr ["cut-case", cs, atom]

pattern ReturnJSON :: Value -> Value
pattern ReturnJSON atoms = Arr ["return", atoms]

pattern LetJSON :: Value -> Value -> Value -> Value
pattern LetJSON arity rhs body = Arr ["let", arity, rhs, body]

pattern AllocJSON :: Value -> Value -> Value
pattern AllocJSON heapVals body = Arr ["alloc", heapVals, body]

instance ToJSON Term where
  -- TODO: all these could be encoded unambiguously with a single character
  toJSON = \case
    CutLambda lam vals -> CutLambdaJSON (tj lam) (tj vals)
    CutCase cs atom -> CutCaseJSON (tj cs) (tj atom)
    Return atoms -> ReturnJSON (tj atoms)
    Let arity rhs body -> LetJSON (tj arity) (tj rhs) (tj body)
    Alloc heapVals body -> AllocJSON (tj heapVals) (tj body)

instance FromJSON Term where
  parseJSON = \case
    CutLambdaJSON lam vals -> CutLambda <$> fj lam <*> fj vals
    CutCaseJSON cs atom -> CutCase <$> fj cs <*> fj atom
    ReturnJSON atoms -> Return <$> fj atoms
    LetJSON arity rhs body -> Let <$> fj arity <*> fj rhs <*> fj body
    AllocJSON heapVals body -> Alloc <$> fj heapVals <*> fj body

    invalid -> typeMismatch "Term" invalid

pattern HeapLambdaJSON :: Value -> Value
pattern HeapLambdaJSON lambda = Arr ["heap-lambda", lambda]

pattern HeapCaseJSON :: Value -> Value
pattern HeapCaseJSON cs = Arr ["heap-case", cs]

pattern HeapTaggedJSON :: Value -> Value -> Value
pattern HeapTaggedJSON ix val = Arr ["heap-tagged", ix, val]

pattern HeapMultiValJSON :: Value -> Value
pattern HeapMultiValJSON vals = Arr ["heap-multi-val", vals]

pattern HeapAtomJSON :: Value -> Value
pattern HeapAtomJSON atom = Arr ["heap-atom", atom]

instance ToJSON HeapVal where
  toJSON = \case
    HeapLambda lam -> HeapLambdaJSON (tj lam)
    HeapCase cs -> HeapCaseJSON (tj cs)
    HeapTagged ix val -> HeapTaggedJSON (tj ix) (tj val)
    HeapMultiVal vals -> HeapMultiValJSON (tj vals)
    HeapAtom atom -> HeapAtomJSON (tj atom)

instance FromJSON HeapVal where
  parseJSON = \case
    HeapLambdaJSON lam -> HeapLambda <$> fj lam
    HeapCaseJSON cs -> HeapCase <$> fj cs
    HeapTaggedJSON ix val -> HeapTagged <$> fj ix <*> fj val
    HeapMultiValJSON vals -> HeapMultiVal <$> fj vals
    HeapAtomJSON atom -> HeapAtom <$> fj atom

    invalid -> typeMismatch "HeapVal" invalid

pattern LambdaJSON :: Value -> Value
pattern LambdaJSON tm = Arr ["lambda-lambda", tm]

pattern OracleJSON :: Value -> Value -> Value
pattern OracleJSON ty cid = Arr ["lambda-oracle", ty, cid]

instance ToJSON Lambda where
  toJSON = \case
    Lambda tm -> LambdaJSON (tj tm)
    Oracle ty cid -> OracleJSON (tj ty) (tj cid)

instance FromJSON Lambda where
  parseJSON = \case
    LambdaJSON tm -> Lambda <$> fj tm
    OracleJSON ty cid -> Oracle <$> fj ty <*> fj cid

    invalid -> typeMismatch "Lambda" invalid

pattern CaseJSON :: Value -> Value
pattern CaseJSON branches = Arr ["case", branches]

instance ToJSON Case where
  toJSON (Case branches) = CaseJSON (tj branches)

instance FromJSON Case where
  parseJSON = \case
    CaseJSON branches -> Case <$> fj branches

    invalid -> typeMismatch "Case" invalid

pattern VariableJSON :: Int -> Int -> Value
pattern VariableJSON level ix = Arr ["variable", Int level, Int ix]

pattern LiteralJSON :: Value -> Value
pattern LiteralJSON lit = Arr ["literal", lit]

pattern TermJSON :: Value -> Value
pattern TermJSON tm = Arr ["term", tm]

pattern HeapValJSON :: Value -> Value
pattern HeapValJSON hv = Arr ["heapval", hv]

instance ToJSON Atom where
  toJSON = \case
    Variable l i -> VariableJSON l i
    Literal lit -> LiteralJSON (tj lit)
    Term tm -> TermJSON (tj tm)
    HeapVal hv -> HeapValJSON (tj hv)

instance FromJSON Atom where
  parseJSON = \case
    VariableJSON l i -> pure (Variable l i)
    LiteralJSON lit -> Literal <$> fj lit
    TermJSON tm -> Term <$> fj tm
    HeapValJSON hv -> HeapVal <$> fj hv

    invalid -> typeMismatch "Atom" invalid

pattern LiteralTextJSON :: Text -> Value
pattern LiteralTextJSON str = Arr ["literal-text", String str]

pattern LiteralWord32JSON :: Word32 -> Value
pattern LiteralWord32JSON word = Arr ["literal-word32", Word word]

instance ToJSON Literal where
  toJSON = \case
    LiteralText str -> LiteralTextJSON str
    LiteralWord32 word -> LiteralWord32JSON word

instance FromJSON Literal where
  parseJSON = \case
    LiteralTextJSON str -> pure $ LiteralText str
    LiteralWord32JSON word -> pure $ LiteralWord32 word

    invalid -> typeMismatch "Literal" invalid
