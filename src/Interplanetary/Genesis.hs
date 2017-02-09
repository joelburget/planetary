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

instance IsString (Location 'Nominal) where
  fromString = Name . fromString

instance Num (Location 'Positional) where
  fromInteger = Index . fromInteger

data Domain :: LocationType -> * where
  NominalDomain :: HashMap Text GenesisTerm -> Domain 'Nominal

  PositionalDomain :: Vector GenesisTerm -> Domain 'Positional

  AtomicDomain :: GenesisTerm -> Domain 'Atomic

deriving instance Show (Domain pos)

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
