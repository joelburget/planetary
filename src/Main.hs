{-# language DataKinds #-}
{-# language OverloadedStrings #-}
module Main where

import qualified Data.Map as Map

import Tower.Genesis
import Tower.Eval

-- Examples:

unit :: GenesisTerm
unit = Product' (NominalDomain Map.empty)

nothing :: GenesisValue 'Nominal 'Additive
nothing = Sum "Nothing" unit

elimNothing :: GenesisCovalue 'Nominal 'Additive
elimNothing = Case $ NominalDomain $ Map.fromList [ ("Nothing", unit) ]

comp :: GenesisTerm
comp = Computation nothing elimNothing

main :: IO ()
main = do
  print comp
  print (step comp)
