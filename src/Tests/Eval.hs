{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Tests.Eval where

import Bound (closed)
import Control.Distributed.Process.Serializable (Serializable)
import Data.Dynamic
import Test.Tasty
import Test.Tasty.HUnit

import Interplanetary.Eval
-- import Interplanetary.Parser.QQ
import Interplanetary.Predefined
import Interplanetary.Syntax

stepTest
  :: String
  -> EvalEnv
  -> TmI
  -> Either Err TmI
  -> TestTree
stepTest name env tm expected = testCase name $
  runEvalM env (step tm) @=? expected

mkForeign :: Serializable a => a -> (UId, Dynamic)
mkForeign val = (mkUid val, toDyn val)

-- TODO: this is awfully kludgy:
-- * uids are duplicated here and in Interplanetary.UIds
-- * we shouldn't need to supply the Uid separately -- it can be derived from
-- the data
simpleEnv :: EvalEnv
simpleEnv =
  ( foreignContinuations
  , uIdMapFromList
    [ mkForeign @Int 1
    , mkForeign @Int 2
    , mkForeign @Int 4
    , mkForeign @String "hello "
    , mkForeign @String "world"
    , mkForeign @String "hello world"
    ]
  )

-- extractAndInlineForeign :: TmI -> (ForeignStore Int Int, TmI)
-- extractAndInlineForeign = _

mkForeignTm :: Serializable a => a -> TmI
mkForeignTm = ForeignDataTm . mkUid

unitTests :: TestTree
unitTests = testGroup "evaluation"
  [ stepTest "1 + 1" simpleEnv
    (Cut
      (Application [mkForeignTm @Int 1, mkForeignTm @Int 1])
      (Value (ForeignFun intOpsId 0)))
    (Right (mkForeignTm @Int 2))
  , stepTest "2 + 2" simpleEnv
    (Cut
      (Application [mkForeignTm @Int 2, mkForeignTm @Int 2])
      (Value (ForeignFun intOpsId 0)))
    (Right (mkForeignTm @Int 4))
  , stepTest "2 - 1" simpleEnv
    (Cut
      (Application [mkForeignTm @Int 2, mkForeignTm @Int 1])
      (Value (ForeignFun intOpsId 1)))
    (Right (mkForeignTm @Int 1))
  , stepTest "\"hello \" <> \"world\"" simpleEnv
    (Cut
      (Application [mkForeignTm @String "hello ", mkForeignTm @String "world"])
      (Value (ForeignFun strOpsId 0)))
    (Right (mkForeignTm @String "hello world"))
  , let Just f = closed (lam @String ["x"] (V"x"))
    in stepTest "application: (\\x -> x) x" simpleEnv
         (Cut (Application [V 0]) (Value f))
         (Right (V 0))
  -- stepTest "application 1" [tm| (\y -> y) x |] (Variable "x")
  ]

runEvalTests :: IO ()
runEvalTests = defaultMain (testGroup "" [unitTests])
