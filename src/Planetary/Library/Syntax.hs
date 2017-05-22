{-# language QuasiQuotes #-}
module Planetary.Library.Syntax where

import Network.IPLD

import Planetary.Core
import Planetary.Support.Parser.QQ

-- Problems:
--   * need list / vector predefined
--   * mutual recursion :(

-- TODO: vector

-- dataTypeTable :: DataTypeTable Cid Int
-- interfaceTable :: InterfaceTable Cid Int
-- ( dataTypeTable :: DataTypeTable Cid Int,
--   interfaceTable :: InterfaceTable Cid Int) = [declarations|
-- data Vector x =

-- data ValTy uid a x =
--   | uid (d:Vector x)
--   | x
--   | a
-- |]
