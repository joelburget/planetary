{-# language DataKinds #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# options_ghc -Wall #-}

module Main where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Text (Text)
import Data.Vector (Vector, (!?))

-- TODO: Atomic also?
data LocationType = Nominal | Positional

data Location :: LocationType -> * where
  Name :: Text -> Location 'Nominal
  Index :: Int -> Location 'Positional

deriving instance Eq (Location a)
deriving instance Ord (Location a)
deriving instance Show (Location a)

{-
data Domain :: LocationType -> * where
  NominalDomain :: Set Text -> Domain 'Nominal

  -- [0..i-1]
  PositionalDomain :: Int -> Domain 'Positional
-}

data Domain :: LocationType -> [LocationType] -> * where
  NominalDomain :: Map Text (GenesisTerm levels)
                -> Domain 'Nominal levels

  PositionalDomain :: Vector (GenesisTerm levels)
                   -> Domain 'Positional levels

deriving instance Eq (Domain pos levels)
deriving instance Show (Domain pos levels)

domainLookup :: Domain pos levels -> Location pos -> Maybe (GenesisTerm levels)
domainLookup (NominalDomain dom) (Name name) = Map.lookup name dom
domainLookup (PositionalDomain vec) (Index ix) = vec !? ix

-- TODO better name
data SumProd = Additive | Multiplicative

-- type Closed x = x '[]

-- TODO we also want let
data GenesisTerm :: [LocationType] -> * where

  Computation :: GenesisValue l ls sumprod
              -> GenesisCovalue l (l ': ls) sumprod
              -> GenesisTerm ls

  Value       :: GenesisValue pos levels sumprod
              -> GenesisTerm levels

  Covalue     :: GenesisCovalue pos levels sumprod
              -> GenesisTerm levels

  Bound       :: Location pos
              -> GenesisTerm (pos ': levels)

  -- Splice
  -- Quote
  --
  -- What language-level support do patches require?

deriving instance Eq (GenesisTerm a)
deriving instance Show (GenesisTerm a)

-- A value is a sum or a product
--
-- A @GenesisValue pos levels sumprod@:
-- * Is itself indexed by @pos@
-- * Has variables bound by levels @levels@
-- * Is a sum or product as decided by @sumprod@
data GenesisValue :: LocationType -> [LocationType] -> SumProd -> * where
  Sum     :: Location pos
          -> GenesisTerm levels
          -> GenesisValue pos levels 'Additive

  Product :: Domain pos levels
          -> GenesisValue pos levels 'Multiplicative

deriving instance Show (GenesisValue pos levels sumprod)

-- A covalue is a case or pattern match
--
-- A @GenesisCovalue levels sumprod@
-- * Is itself indexed by @pos@
-- * Has variables bound by levels @levels@
-- * Is a sum or product as decided by @sumprod@
data GenesisCovalue :: LocationType -> [LocationType] -> SumProd -> * where
  Case  :: Domain pos levels
        -> GenesisCovalue pos levels 'Additive

  Match :: GenesisTerm levels
        -> GenesisCovalue pos (pos ': levels) 'Multiplicative

deriving instance Show (GenesisCovalue pos levels sumprod)

step :: GenesisTerm levels -> GenesisTerm levels
step v@(Value _) = v
step c@(Covalue _) = c
step (Computation (Sum pos body) (Case branches)) =
  case domainLookup branches pos of
    -- TODO define body in case
    Just result -> close1 result body
    Nothing -> error $ "failed lookup: " ++ show pos
-- TODO define fields in body
step (Computation (Product subs) (Match body)) = close2 body _subs

-- this is so wrong
close1 :: GenesisTerm (pos ': levels)
       -> GenesisTerm levels
       -> GenesisTerm levels
close1 = undefined

close2 :: GenesisTerm (pos ': levels)
       -> Domain pos levels
       -> GenesisTerm levels
close2 = undefined

-- this is also wrong
open :: GenesisTerm levels
     -> (Location pos, GenesisTerm levels)
     -> GenesisTerm (pos ': levels)
open = undefined

-- Examples:

-- | Transfor an expression into the representation of that epxression
--
-- When do you actually need this in the genesis language? Well, our goal is to
-- *enhance* the language, not create new ones from scratch. Indicating we want
-- to borrow from the base language.
quote :: GenesisTerm a -> GenesisTerm a
quote = undefined

unit :: GenesisTerm a
unit = Value (Product Map.empty)

nothing :: GenesisValue 'Nominal a 'Additive
nothing = Sum (Name "Nothing") unit

elimNothing :: GenesisCovalue 'Nominal ('Nominal ': a) 'Additive
elimNothing =
  let body = Case $ Map.fromList [ (Name "Nothing", unit) ]
  in body

comp :: GenesisTerm '[]
comp = Computation nothing elimNothing

main :: IO ()
main = putStrLn "here"
