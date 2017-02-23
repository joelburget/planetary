{-# language OverloadedLists #-}
import Data.Maybe
import Test.Tasty
import Test.Tasty.HUnit

import Interplanetary.Examples
import Interplanetary.Genesis
import Interplanetary.Typecheck

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "ipc" [unitTests]

unitTests :: TestTree
unitTests = testGroup "ipc unit tests"
  [ testCase "expected failure" $ assertBool "" (isJust (topCheck badUnitT))
  , testCase "check nothingT" $ assertBool "" (isNothing (topCheck nothingT))
  , testCase "check computation" $ assertBool "" (isNothing (topCheck compT))
  ]

unifyTests :: TestTree
unifyTests = testGroup "ipc unification tests"
  [ testCase "1" $ assertBool "" $ isRight $ runTypingContext $
      unify (TypeMetavar 1) TypeLiteralText
  ]
