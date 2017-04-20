{-# language QuasiQuotes #-}
module Tests.Eval where

import qualified Data.IntMap as IntMap
import Test.Tasty
import Test.Tasty.HUnit
import Text.Trifecta

import Interplanetary.Parser.QQ

stepTest
  :: String
  -> EvalEnv
  -> TmI
  -> Either Err TmI
  -> TestTree
stepTest name env tm expected = testCase name $
  runEvalM env (step tm) @=? expected

unitTests :: TestTree
unitTests = testGroup "evaluation"
  [ stepTest "application 1" [tm| (\y -> y) x |] (Variable "x")
  , stepTest "application 2" [tm| (\x -> x) x |] (Variable "x")
  ]
