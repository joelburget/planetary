{-# language DataKinds #-}
{-# language OverloadedStrings #-}
module Planetary.Core.Eval.Test where

import Bound (closed)
import Prelude hiding (not)
import Network.IPLD as IPLD
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Support.Ids

stepTest
  :: String
  -> EvalEnv
  -> Int
  -> TmI
  -> Either Err TmI
  -> TestTree
stepTest name env steps tm expected =
  let applications = iterate (step =<<) (pure tm)
      actual = applications !! steps

  in testCase name $ do
    result <- runEvalM env [] actual

    fst result @?= expected

bool :: Int -> Tm 'TM Cid b
bool i = DataTm boolId i []

unitTests :: TestTree
unitTests  =
  let emptyEnv :: EvalEnv
      emptyEnv = EvalEnv mempty mempty

      -- true, false :: forall a b. Tm 'TM Cid a b
      false = bool 0
      true = bool 1

      not = Case boolId
        [ ([], abstract0 true)
        , ([], abstract0 false)
        ]
      -- boolOfInt = Case boolId
      --   [ ([], abstract0 one)
      --   , ([], abstract0 zero)
      --   ]

  in testGroup "evaluation"
       [ testGroup "functions"
         [ let x = V 0
               -- tm = [tmExp| (\y -> y) x |]
               Just lam = closed (Lam ["X"] (V"X"))
               tm = Cut (Application [x]) (Value lam)
           in stepTest "application 1" emptyEnv 1 tm (Right x)
         ]
       , testGroup "case"
           [ stepTest "case False of { False -> True; True -> False }"
               emptyEnv 1
             -- [tmExp|
             --   case false of
             --     boolId:
             --       | -> one
             --       | -> zero
             -- |]
             -- [ ("false", false)
             -- , ("bool", bool)
             -- , ("one", one)
             -- , ("zero", zero)
             -- ]
             (Cut not false)
             (Right true)
           , stepTest "case True of { False -> True; True -> False }"
               emptyEnv 1
             (Cut not true)
             (Right false)

         , stepTest "not false" emptyEnv 1
           (Cut not false)
           (Right true)
           ]
       , let ty :: Polytype Cid
             ty = Polytype [] (DataTy boolId [])
             -- TODO: remove shadowing
             Just tm = closeVar ("x", 0) $ let_ "x" ty false (V"x")
         in stepTest "let x = false in x" emptyEnv 1 tm (Right false)

       , let
             ty = Polytype [] (DataTy boolId [])
             -- Just tm = cast [tmExp|
             --   let x: forall. bool = false in
             --     let y: forall. bool = not x in
             --       not y
             -- |]
             Just tm = closeVar ("x", 0) $
                  let_ "x" ty false $
                    let_ "y" ty (Cut not (V"x")) $
                      Cut not (V"y")
         in stepTest "let x = false in let y = not x in not y"
              emptyEnv 3 tm (Right false)

       -- , let
       --   in stepTest ""
       ]

runEvalTests :: IO ()
runEvalTests = defaultMain unitTests
