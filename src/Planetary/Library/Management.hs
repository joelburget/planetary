{-# language QuasiQuotes #-}
module Planetary.Library.Management (resolvedDecls) where

import NeatInterpolation

import Planetary.Core
-- import Planetary.Support.NameResolution
import Planetary.Support.Parser

decls = forceDeclarations [text|
data LanguageDiff =
  | <Apply {<Syntax> -> <Syntax>} {<Semantics> -> <Semantics>}>
|]

resolvedDecls :: ResolvedDecls
resolvedDecls = mempty
-- Right resolvedDecls = resolveDecls (todo "predefined") decls
