{-# language OverloadedStrings #-}
{-# language OverloadedLists #-}

module Interplanetary.StrNat where

import Interplanetary.Syntax
import Interplanetary.Meta

-- A simple language of strings and naturals.
--
-- This is the language E from PFPL

pattern NatStrTy :: TmI
pattern NatStrTy = DataTm natStrTyUid 0 []

pattern Nat :: TmI
pattern Nat = DataTm natStrUid 0 []

pattern Str :: TmI
pattern Str = DataTm natStrUid 1 []

typeSyntax :: TmI
typeSyntax = NatStrTy
  [ Unit -- num
  , Unit -- str
  ]

-- let's describe the syntax

termSyntax :: TmI
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
language :: TmI
language = Product'
  -- question: types don't appear in the syntax?
  [ termSyntax

  -- design goal: typechecking should reveal a stack / evaluation state
  , todo "typechecking"

  -- design goal: as should evaluation
  , todo "evaluation"
  ]
