{-# language DataKinds #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language StandaloneDeriving #-}
{-# language KindSignatures #-}
{-# language LambdaCase #-}
{-# language PatternSynonyms #-}
{-# language FlexibleInstances #-}
{-# language ViewPatterns #-}

module Interplanetary.Genesis where

import Data.Aeson
import Data.Aeson.Types (Parser, typeMismatch)
import Data.Foldable (asum)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import Data.String
import Data.Text (Text)
import Data.Vector (Vector, (!?))

import Interplanetary.Patterns

newtype MultiHash = MultiHash Text deriving Show

data LocationType = Nominal | Positional | Atomic

data Location :: LocationType -> * where
  Name :: Text -> Location 'Nominal
  Index :: Int -> Location 'Positional
  Atom :: Location 'Atomic

deriving instance Eq (Location a)
deriving instance Show (Location a)

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

instance IsString (Location 'Nominal) where
  fromString = Name . fromString

instance Num (Location 'Positional) where
  fromInteger = Index . fromInteger

data Domain :: LocationType -> * where
  NominalDomain :: HashMap Text GenesisTerm -> Domain 'Nominal

  PositionalDomain :: Vector GenesisTerm -> Domain 'Positional

  AtomicDomain :: GenesisTerm -> Domain 'Atomic

deriving instance Show (Domain pos)

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

domainLookup :: Domain pos1 -> Location pos2 -> Maybe GenesisTerm
domainLookup (NominalDomain dom) (Name name) = HashMap.lookup name dom
domainLookup (PositionalDomain vec) (Index ix) = vec !? ix
domainLookup (AtomicDomain it) Atom = Just it
domainLookup _ _ = Nothing

mapDomain :: (GenesisTerm -> GenesisTerm) -> Domain pos -> Domain pos
mapDomain f = \case
  NominalDomain dom -> NominalDomain $ f <$> dom
  PositionalDomain vec -> PositionalDomain $ f <$> vec
  AtomicDomain it -> AtomicDomain (f it)

nominalDomain' :: [(Text, GenesisTerm)] -> Domain 'Nominal
nominalDomain' = NominalDomain . HashMap.fromList

-- TODO better name
data SumProd = Additive | Multiplicative

data GenesisTerm :: * where

  Computation :: GenesisValue l sumprod
              -> GenesisCovalue l sumprod
              -> GenesisTerm

  Value       :: GenesisValue pos sumprod
              -> GenesisTerm

  Covalue     :: GenesisCovalue pos sumprod
              -> GenesisTerm

  Bound       :: Int          -- ^ level
              -> Location pos -- ^ position with that level
              -> GenesisTerm

  -- TODO: subsumed by Oracle?
  Quote       :: GenesisTerm -> GenesisTerm

  Splice      :: GenesisTerm -> GenesisTerm

  -- TODO: we might also want a dynamic here. so we can actually access this
  -- external value.
  Oracle      :: MultiHash -> GenesisTerm

  -- Let
  --
  -- What language-level support do patches require? In a surprising twist,
  -- maybe none!

-- deriving instance Eq GenesisTerm
deriving instance Show GenesisTerm

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

-- A value is a sum or a product.
--
-- A @GenesisValue pos sumprod@:
-- * Is itself indexed by @pos@ (@Atomic@, @Nominal@, or @Positional@)
-- * Is a sum or product as decided by @sumprod@
--
-- Both sums and products come in three variations:
-- * @Atomic@ - A single value
-- * @Nominal@ - Indexed by name
-- * @Positional@ - Indexed by position
--
-- * @Sum Atomic@, @Product Atomic@ - Both hold a single value (in the
--   applicand position of a function application).
--   - @Sum Atomic@ ~ "One of these 1 things"
--   - @Product Atomic@ ~ "All of these 1 things"
-- * @Sum Nominal@ - One of a named collection
-- * @Sum Positional@ - One of an anonymous, sized collection
-- * @Product Nominal@ - A collection of values indexed by name
-- * @Product Positional@ - An array of values indexed by position
data GenesisValue :: LocationType -> SumProd -> * where
  Sum     :: Location pos
          -> GenesisTerm
          -> GenesisValue pos 'Additive

  Product :: Domain pos
          -> GenesisValue pos 'Multiplicative

deriving instance Show (GenesisValue pos sumprod)
-- deriving instance Generic (GenesisValue pos sumprod)

instance ToJSON (GenesisValue pos sumprod) where
  toJSON = \case
    Sum loc tm  -> Value_Sum (tj loc) (tj tm)
    Product dom -> Value_Product (tj dom)

--

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

parseValueJSON :: Value -> Parser GenesisTerm
parseValueJSON val = asum
  [ Value <$> parseAtomicSum val
  , Value <$> parseNominalSum val
  , Value <$> parsePositionalSum val
  , Value <$> parseProductAtomic val
  , Value <$> parseProductNominal val
  , Value <$> parseProductPositional val
  ]

--

pattern Sum' :: Location pos -> GenesisTerm -> GenesisTerm
pattern Sum' loc tm = Value (Sum loc tm)

pattern Product' :: Domain pos -> GenesisTerm
pattern Product' dom = Value (Product dom)

-- A covalue is a case or pattern match.
--
-- A @GenesisCovalue sumprod@
-- * Is itself indexed by @pos@
-- * Is a sum or product as decided by @sumprod@
--
-- Both sums and products come in three variations:
-- * @Atomic@ - A lambda
-- * @Nominal@ - Indexed by name
-- * @Positional@ - Indexed by position
--
-- @Case Atomic@, @Match Atomic@ - Both are representations of lambdas
--   - @Case Atomic@ ~ "Consume one of these one things"
--   - @Match Atomic@ ~ "Consume all of these one things"
-- @Case Nominal@ - Match named, unordered cases
-- @Case Positional@ - Match an ordered collection of anonymous cases
-- @Match Nominal@ - Destructure a named object
-- @Match Positional@ - Destructure an array
--
-- TODO: Both values and covalues look the same in the Atomic case -- should we
-- change representation?
data GenesisCovalue :: LocationType -> SumProd -> * where
  Case  :: Domain pos
        -> GenesisCovalue pos 'Additive

  Match :: GenesisTerm
        -> GenesisCovalue pos 'Multiplicative

pattern Case' :: Domain pos -> GenesisTerm
pattern Case' dom = Covalue (Case dom)

pattern Match' :: GenesisTerm -> GenesisTerm
pattern Match' tm = Covalue (Match tm)

deriving instance Show (GenesisCovalue pos sumprod)
-- deriving instance Generic (GenesisValue pos sumprod)

instance ToJSON (GenesisCovalue pos sumprod) where
  toJSON = \case
    Case dom -> Covalue_Case (tj dom)
    Match tm -> Covalue_Match (tj tm)

--

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

parseCovalueJSON :: Value -> Parser GenesisTerm
parseCovalueJSON val = asum
  [ Covalue <$> parseAtomicCase val
  , Covalue <$> parseNominalCase val
  , Covalue <$> parsePositionalCase val
  , Covalue <$> parseMatch val
  ]
