module Tests.Parser where

import Data.Either
import qualified Data.IntMap as IntMap
import Test.Tasty
import Test.Tasty.HUnit

import Interplanetary.Syntax
import Interplanetary.Parser

-- "(\\x -> x : Unit -> [e]Unit)"
-- "(\\x -> x : Unit -> [o]Unit)"
-- "unit : Unit"

unitTests :: TestTree
unitTests = testGroup "checking"
  [ testCase "X" $
      runTokenParse parseTyVar "X" @=? Right 0
  -- , testCase "handle" $
  ]
