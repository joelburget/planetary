{-# language QuasiQuotes #-}
module Planetary.Library.Syntax where

import Network.IPLD

import Planetary.Core
import Planetary.Support.Parser.QQ

-- Problems:
--   * need list / vector predefined
--   * mutual recursion :(

-- dataTypeTable :: DataTypeTable Cid Int
-- interfaceTable :: InterfaceTable Cid Int
-- (dataTypeTable, interfaceTable) = [declarations|
-- ValTy = data =
-- |]
