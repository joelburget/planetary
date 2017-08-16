{-# language OverloadedLists #-}
{-# language QuasiQuotes #-}
{-# language TypeFamilies #-}
module Planetary.Library.Meta () where

decls = forceDeclarations [text|
data Colors =
  | Red
  | Green

addColor = letrec
  addConstructor
    : {<Data> -> [Abort]<Data>}
    = \data -> case data of
      Data:
        -- man, this would be nicer with patterns
        | <sum ctrs> -> case ctrs of
          List:
            | <cons ctr ctrs'> -> case ctrs' of
              List:
                | <cons ctr' ctrs''> -> case ctrs'' of
                  List:
                    | <cons _ _> ->
                    | <nil>      -> ...
                | <nil> -> throw
            | <nil> -> throw

reflection = letrec
  reified
    : {<Term>}
    -- an empty list in a list
    = \-> reify <List.1 <List.0> <List.0>>

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
      List:
        | <nil> -> <List.0>
        | <cons l ls> -> <List.1 (length l) ...>
|]
