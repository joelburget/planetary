{-# language QuasiQuotes #-}
module Planetary.Library.Meta.Test where

import Data.Either (fromRight)
import EasyTest
import NeatInterpolation

import Planetary.Core
import Planetary.Library
import Planetary.Support.Parser

testRunner :: TmI -> Test ()
testRunner = undefined

-- check reflect / reify roundtrip
unitTests :: Test ()
unitTests = scope "meta" $ testRunner $
  fromRight (error "expected resolution") $ resolve $ fst $ forceTm [text|
|]
