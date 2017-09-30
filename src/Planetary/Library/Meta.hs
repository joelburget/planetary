{-# language OverloadedLists #-}
{-# language QuasiQuotes #-}
{-# language TypeFamilies #-}
module Planetary.Library.Meta (resolvedDecls) where

import NeatInterpolation

import Planetary.Core
import Planetary.Support.Parser

decls = forceDeclarations [text|
data Colors =
  | Red
  | Green

addColor = letrec
  addConstructor
    : {<Data> -> [Abort]<Data>}
    = \data -> case data of
      -- man, this would be nicer with patterns
      | <sum ctrs> -> case ctrs of
        | <cons ctr ctrs'> -> case ctrs' of
          | <cons ctr' ctrs''> -> case ctrs'' of
            | <cons _ _> ->
            | <nil>      -> ...
          | <nil> -> throw
        | <nil> -> throw

reflection = letrec
  reified
    : {<Term>}
    -- an empty list in a list
    = \-> reify <List.1 <List.0> <List.0>>

  -- TODO: do we need to supply a typechecker specific to the language we're
  -- working in? `typecheck` should maybe be `typecheckCoreFrank`. Same deal
  -- for the eval and reify.
  typechecked
    : {<TypecheckedTerm>}
    = \-> typecheck reified

  -- should this be typechecked term?
  evaled
    : {<TypecheckedTerm>}
    = \-> eval typechecked

  -- TODO: compare this vs evaled
  -- return the length of all lists in the main list
  reified
    : {<Fix <ListF> <Int>>}
    = \-> case reify typechecked of
      | <nil> -> <List.0>
      | <cons l ls> -> <List.1 (length l) ...>
|]

resolvedDecls :: ResolvedDecls
resolvedDecls = mempty -- TODO
