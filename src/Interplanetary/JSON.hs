{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# language DataKinds #-}
{-# language OverloadedStrings #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}

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

pattern ValueBindJSON :: Value -> Value
pattern ValueBindJSON ann = Arr ["bind-v", ann]

pattern TypeBindJSON :: Value
pattern TypeBindJSON = Arr ["bind-t"]

pattern CutLambdaJSON :: Value -> Value -> Value
pattern CutLambdaJSON lam args = Arr ["cut-lambda", lam, args]

instance ToJSON ann => ToJSON (Binder ann) where
  toJSON = \case
    ValueBind ann -> ValueBindJSON (tj ann)
    TypeBind -> TypeBindJSON

instance FromJSON ann => FromJSON (Binder ann) where
  parseJSON = \case
    ValueBindJSON ann -> ValueBind <$> fj ann
    TypeBindJSON -> pure TypeBind
    invalid -> typeMismatch "Binder" invalid

instance ToJSON Type where
  toJSON = todo "ToJSON Type"

instance FromJSON Type where
  parseJSON = todo "FromJSON Type"

instance ToJSON ann => ToJSON (Term ann) where
  -- TODO: all these could be encoded unambiguously with a single character
  toJSON = \case
    CutLambda lam vals -> CutLambdaJSON (tj lam) (tj vals)

instance FromJSON ann => FromJSON (Term ann) where
  parseJSON = \case
    CutLambdaJSON lam vals -> CutLambda <$> fj lam <*> fj vals

    invalid -> typeMismatch "Term" invalid

instance ToJSON ann => ToJSON (HeapVal ann) where
  toJSON = todo "ToJSON HeapVal"

instance FromJSON ann => FromJSON (HeapVal ann) where
  parseJSON = todo "FromJSON HeapVal"

instance ToJSON ann => ToJSON (Lambda ann) where
  toJSON = todo "ToJSON Lambda"

instance FromJSON ann => FromJSON (Lambda ann) where
  parseJSON = todo "FromJSON Lambda"

instance ToJSON ann => ToJSON (Case ann) where
  toJSON = todo "ToJSON Case"

instance FromJSON ann => FromJSON (Case ann) where
  parseJSON = todo "FromJSON Case"

instance ToJSON Atom where
  toJSON = todo "ToJSON Atom"

instance FromJSON Atom where
  parseJSON = todo "FromJSON Atom"

instance ToJSON Literal where
  toJSON = todo "ToJSON Literal"

instance FromJSON Literal where
  parseJSON = todo "FromJSON Literal"

