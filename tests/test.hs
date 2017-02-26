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
  [ testCase "1" $ assertBool "" $ isRight $ runTypingContext $ do
      v1 <- freeVar
      v2 <- freeVar
      let tm1 = TypeMultiVal' [v1, TypeLit TypeLiteralText]
          tm2 = TypeMultiVal' [TypeLit TypeLiteralWord32, v2]
      tm1 =:= tm2
  ]
