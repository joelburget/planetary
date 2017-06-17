{-# language QuasiQuotes #-}
module Planetary.Library.Management where

decls = forceDeclarations [text|
data LanguageDiff =
  | Apply {Syntax -> Syntax} {Semantics -> Semantics}
|]
