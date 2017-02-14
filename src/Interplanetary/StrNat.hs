{-# language OverloadedStrings #-}
{-# language OverloadedLists #-}

module Interplanetary.StrNat where

import Interplanetary.Genesis
import Interplanetary.Meta

-- A simple language of strings and naturals.
--
-- This is the language E from PFPL

{-
uidOracle :: GenesisTerm
uidOracle = Oracle (InlineText "PRIM_UID_ORACLE")

-- The oracle yields a unique id, which we consume to produce an opaque type
uniqueTyDesc :: GenesisTerm
uniqueTyDesc = ComputationTyRep (OpaqueTyRep (Bound 0 Atom)) uidOracle
-}

typeSyntax :: GenesisTerm
typeSyntax = Product'
  [ Unit -- num
  , Unit -- str
  ]

-- let's describe the syntax

termSyntax :: GenesisTerm
termSyntax =
 let e = Bound 0 Atom -- It would be nice to do this in a less low-level way
 in Product'
      [ Word32TyRep -- num
      , TextTyRep -- str
      , Product' [e, e] -- plus
      , Product' [e, e] -- times
      , Product' [e, e] -- cat
      , Product' [e] -- len
      -- TODO: var, let
      ]

-- now to define the statics

-- TODO: need to declare the type of a language somewhere
--
-- question: This is a `[[ Language ]]_Genesis`. Should that be declared
-- somewhere?
language :: GenesisTerm
language = Product'
  -- question: types don't appear in the syntax?
  [ termSyntax

  -- design goal: typechecking should reveal a stack / evaluation state
  , todo "typechecking"

  -- design goal: as should evaluation
  , todo "evaluation"
  ]
