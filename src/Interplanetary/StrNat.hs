{-# language OverloadedStrings #-}
{-# language OverloadedLists #-}

module Interplanetary.StrNat where

import Interplanetary.Genesis

-- A simple language of strings and naturals.
--
-- This is the language E from PFPL

unit :: GenesisTerm
unit = Product' (nominalDomain' [])

typeSyntax :: GenesisTerm
typeSyntax = Product' $ nominalDomain'
  [ ("num", unit)
  , ("str", unit)
  ]

termSyntax :: GenesisTerm
termSyntax = Product' $ PositionalDomain
  [
  ]

-- TODO: need to declare the type of a language somewhere
--
-- question: This is a `[[ Language ]]_Genesis`. Should that be declared
-- somewhere?
language :: GenesisTerm
language = Product' $ nominalDomain'
  -- question: types don't appear in the syntax?
  [ ("syntax", termSyntax)

  -- design goal: typechecking should reveal a stack / evaluation state
  , ("typechecking", todo)

  -- design goal: as should evaluation
  , ("evaluation", todo)
  ]
