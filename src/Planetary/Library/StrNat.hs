{-# language OverloadedLists #-}
{-# language QuasiQuotes #-}
{-# language TypeFamilies #-}
module Planetary.Library.StrNat (resolvedDecls) where

import Data.Text (Text)
import NeatInterpolation
import Network.IPLD (Cid)

import Planetary.Core
import Planetary.Support.NameResolution
import Planetary.Support.Parser
import Planetary.Util

decls = forceDeclarations [text|
data ExprF Expr =
  | <nat <foreignTm>>
  | <str <foreignTm>>
  | <addExpr Expr Expr>
  | <catExpr Expr Expr>

semantics = letrec
  -- TODO: this is ugly
  foreignValue
    : forall. {<Syntax> -> <Syntax>}
    = \x -> <Tm.2 x>

  eval
    : forall. {<Expr <Expr>> -> <Syntax <Syntax>>}
    = \expr -> case expr of
      | <nat n>       -> foreignValue n
      | <str str>     -> foreignValue str
      | <addExpr l r> -> Application (foreignValue add) (vector l r)
      | <catExpr l r> -> Application (foreignValue cat) (vector l r)
in eval
|]

-- TODO:
-- * sub in add, cat

predefined :: UIdMap Text Cid
predefined = mempty -- TODO
  -- [ ("add", _)
  -- , ("cat", _)
  -- , ("vector", _)
  -- ]

resolvedDecls :: ResolvedDecls
resolvedDecls = mempty
-- Right resolvedDecls = resolveDecls predefined decls
