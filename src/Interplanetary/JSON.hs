{-# OPTIONS_GHC -fno-warn-orphans #-}
-- I'm not sure how I feel about this. Another option is to create a newtype
-- wrapper just for GenesisTerm, make that an instance, and move the rest of
-- these into just functions.

{-# language DataKinds #-}
{-# language OverloadedStrings #-}
{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}

module Interplanetary.JSON where

import Data.Aeson
import Data.Aeson.Types (Parser, typeMismatch)
import Data.Foldable (asum)

import Interplanetary.Genesis
import Interplanetary.Patterns

instance ToJSON (Location loc) where
  toJSON = \case
    Name n  -> Location'Nominal n
    Index n -> Location'Positional n
    Atom    -> Location'Atomic

instance FromJSON (Location 'Nominal) where
  parseJSON (Location'Nominal text) = pure (Name text)
  parseJSON invalid = typeMismatch "Location 'Nominal" invalid

instance FromJSON (Location 'Positional) where
  parseJSON (Location'Positional i) = pure (Index i)
  parseJSON invalid = typeMismatch "Location 'Positional" invalid

instance FromJSON (Location 'Atomic) where
  parseJSON Location'Atomic = pure Atom
  parseJSON invalid = typeMismatch "Location 'Atomic" invalid

instance ToJSON (Domain loc) where
  toJSON = \case
    NominalDomain m      -> Domain'Nominal (tj m)
    PositionalDomain vec -> Domain'Positional (tj vec)
    AtomicDomain tm      -> Domain'Atomic (tj tm)

instance FromJSON (Domain 'Nominal) where
  parseJSON (Domain'Nominal (Object hmap)) = NominalDomain <$> mapM parseJSON hmap
  parseJSON invalid = typeMismatch "Domain 'Nominal" invalid

instance FromJSON (Domain 'Positional) where
  parseJSON (Domain'Nominal (Array vec)) = PositionalDomain <$> mapM parseJSON vec
  parseJSON invalid = typeMismatch "Domain 'Positional" invalid

instance FromJSON (Domain 'Atomic) where
  parseJSON (Domain'Atomic obj) = AtomicDomain <$> parseJSON obj
  parseJSON invalid = typeMismatch "Domain 'Atomic" invalid

instance ToJSON GenesisTerm where
  -- TODO: all these could be encoded unambiguously with a single character
  toJSON = \case
    Computation val coval     -> Term_Computation (tj val) (tj coval)
    Value val                 -> Term_Value (tj val)
    Covalue coval             -> Term_Covalue (tj coval)
    Bound level loc           -> Term_Bound (tj level) (tj loc)
    Quote tm                  -> Term_Quote (tj tm)
    Splice tm                 -> Term_Splice (tj tm)
    Oracle (MultiHash addr)   -> Term_Oracle addr

instance FromJSON GenesisTerm where
  parseJSON = \case
    (Term_Computation val coval) -> asum
      [ Computation <$> parseAtomicSum val <*> parseAtomicCase coval
      , Computation <$> parseNominalSum val <*> parseNominalCase coval
      , Computation <$> parsePositionalSum val <*> parsePositionalCase coval
      , Computation <$> parseProductAtomic val <*> parseMatch coval
      , Computation <$> parseProductNominal val <*> parseMatch coval
      , Computation <$> parseProductPositional val <*> parseMatch coval
      ]
    (Term_Value val) -> parseValueJSON val
    (Term_Covalue coval) -> parseCovalueJSON coval

    (Term_Bound level Location'Atomic) -> Bound <$> fj level <*> pure Atom
    (Term_Bound level (Location'Nominal name))
      -> Bound <$> fj level <*> pure (Name name)
    (Term_Bound level (Location'Positional ix))
      -> Bound <$> fj level <*> pure (Index ix)

    (Term_Quote tm) -> Quote <$> fj tm
    (Term_Splice tm) -> Splice <$> fj tm
    (Term_Oracle hash) -> pure $ Oracle $ MultiHash hash
    invalid -> typeMismatch "GenesisTerm" invalid

instance ToJSON (GenesisValue pos sumprod) where
  toJSON = \case
    Sum loc tm  -> Value_Sum (tj loc) (tj tm)
    Product dom -> Value_Product (tj dom)

parseValueJSON :: Value -> Parser GenesisTerm
parseValueJSON val = asum
  [ Value <$> parseAtomicSum val
  , Value <$> parseNominalSum val
  , Value <$> parsePositionalSum val
  , Value <$> parseProductAtomic val
  , Value <$> parseProductNominal val
  , Value <$> parseProductPositional val
  ]

parseAtomicSum :: Value -> Parser (GenesisValue 'Atomic 'Additive)
parseAtomicSum (Value_Sum Location'Atomic tm) = Sum Atom <$> fj tm
parseAtomicSum invalid = typeMismatch "GenesisValue 'Atomic 'Additive" invalid

parseNominalSum :: Value -> Parser (GenesisValue 'Nominal 'Additive)
parseNominalSum (Value_Sum (Location'Nominal name) tm)
  = Sum (Name name) <$> fj tm
parseNominalSum invalid
  = typeMismatch "GenesisValue 'Nominal 'Additive" invalid

parsePositionalSum :: Value -> Parser (GenesisValue 'Positional 'Additive)
parsePositionalSum (Value_Sum (Location'Positional ix) tm)
  = Sum (Index ix) <$> fj tm
parsePositionalSum invalid
  = typeMismatch "GenesisValue 'Positional 'Additive" invalid

parseProductAtomic :: Value -> Parser (GenesisValue 'Atomic 'Multiplicative)
parseProductAtomic (Value_Product dom) = Product <$> fj dom
parseProductAtomic invalid
  = typeMismatch "GenesisValue 'Atomic 'Multiplicative" invalid

parseProductNominal :: Value -> Parser (GenesisValue 'Nominal 'Multiplicative)
parseProductNominal (Value_Product dom) = Product <$> fj dom
parseProductNominal invalid
  = typeMismatch "GenesisValue 'Nominal 'Multiplicative" invalid

parseProductPositional :: Value -> Parser (GenesisValue 'Positional 'Multiplicative)
parseProductPositional (Value_Product dom) = Product <$> fj dom
parseProductPositional invalid
  = typeMismatch "GenesisValue 'Positional 'Multiplicative" invalid


instance ToJSON (GenesisCovalue pos sumprod) where
  toJSON = \case
    Case dom -> Covalue_Case (tj dom)
    Match tm -> Covalue_Match (tj tm)

parseCovalueJSON :: Value -> Parser GenesisTerm
parseCovalueJSON val = asum
  [ Covalue <$> parseAtomicCase val
  , Covalue <$> parseNominalCase val
  , Covalue <$> parsePositionalCase val
  , Covalue <$> parseMatch val
  ]

parseAtomicCase :: Value -> Parser (GenesisCovalue 'Atomic 'Additive)
parseAtomicCase (Covalue_Case (Domain'Atomic dom))
  = Case . AtomicDomain <$> fj dom
parseAtomicCase invalid
  = typeMismatch "GenesisCovalue 'Atomic 'Additive" invalid

parseNominalCase :: Value -> Parser (GenesisCovalue 'Nominal 'Additive)
parseNominalCase (Covalue_Case (Domain'Nominal dom))
  = Case . NominalDomain <$> fj dom
parseNominalCase invalid
  = typeMismatch "GenesisCovalue 'Nominal 'Additive" invalid

parsePositionalCase :: Value -> Parser (GenesisCovalue 'Positional 'Additive)
parsePositionalCase (Covalue_Case (Domain'Positional dom))
  = Case . PositionalDomain <$> fj dom
parsePositionalCase invalid
  = typeMismatch "GenesisCovalue 'Positional 'Additive" invalid

parseMatch :: Value -> Parser (GenesisCovalue a 'Multiplicative)
parseMatch (Covalue_Match tm) = Match <$> fj tm
parseMatch invalid = typeMismatch "GenesisCovalue a 'Multiplicative" invalid
