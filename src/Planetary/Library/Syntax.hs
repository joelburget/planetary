{-# language QuasiQuotes #-}
{-# language ScopedTypeVariables #-}
module Planetary.Library.Syntax where

import Network.IPLD

import Planetary.Core
import Planetary.Support.Parser.QQ

-- Problems: (TODO)
--   * need list / vector predefined
--   * mutual recursion :(

dataTypeTable :: DataTypeTable Cid Int
interfaceTable :: InterfaceTable Cid Int
( dataTypeTable :: DataTypeTable Cid Int,
  interfaceTable :: InterfaceTable Cid Int,
  _,
  _) = [declarations|
data Vector x = -- TODO

data ValTy uid a x =
  | uid <Vector x>
  | x
  | a
|]
