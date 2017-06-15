{-# language QuasiQuotes #-}
module Planetary.Library.Management where

import Planetary.Support.QQ

decls = [declarations|
data Expr f =
  <nat <foreignTm>>
  | <str <foreignTm>>
  | <addExpr f f>
  | <catExpr f f>

semantics = letrec
  eval : forall. {<Expr <Expr>> -> <Syntax <Syntax>>}
       = \expr -> case expr of
         Expr:
           | <nat n> -> <foreignTm n>
           | <str str> -> <foreignTm str>
           | <addExpr l r> -> <cut <apply <vector l r>> <value <foreignTm add>>
           | <catExpr l r> -> <cut <apply <vector l r>> <value <foreignTm cat>>
|]

-- TODO:
-- * define foreignTm, cut, apply, etc
-- * sub in add, cat

predefined :: UIdMap Text Cid
predefined = uIdMapFromList
  [ (add, _)
  , (cat, _)
  ]

Right resolved = nameResolution decls predefined
