{-# language QuasiQuotes #-}
module Planetary.Library.Management where

import Planetary.Support.Parser.QQ

[declarations|
data LanguageDiff =
  | Apply {Syntax -> Syntax} {Semantics -> Semantics}
|]
