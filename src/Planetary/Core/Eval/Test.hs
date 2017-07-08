{-# language DataKinds #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Planetary.Core.Eval.Test (unitTests, stepTest) where

import Control.Lens
import qualified Data.HashMap.Strict as HashMap
import Data.Monoid ((<>))
import NeatInterpolation
import Network.IPLD as IPLD
import Prelude hiding (not)
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Support.Ids
import Planetary.Support.NameResolution (resolveTm)
import Planetary.Support.Parser (forceTm)
import Planetary.Library.FrankExamples as Frank
import Planetary.Library.HaskellForeign (mkForeignTm)

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

runTest
  :: String
  -> EvalEnv
  -> TmI
  -> Either Err TmI
  -> TestTree
runTest name env tm expected = testCase name $ do
  result <- run env [] tm
  fst result @?= expected

bool :: Int -> Tm Cid
bool i = DataConstructor boolId i []

unitTests :: TestTree
unitTests  =
  let emptyEnv :: EvalEnv
      emptyEnv = EvalEnv mempty mempty

      -- true, false :: forall a b. Tm Cid a b
      false = bool 0
      true = bool 1

      not = Case boolId
        [ ([], true)
        , ([], false)
        ]
      -- boolOfInt = Case boolId
      --   [ ([], one)
      --   , ([], zero)
      --   ]

  in testGroup "evaluation"
       [ testGroup "functions"
         [ let x = BV 0 0
               -- tm = forceTm "(\y -> y) x"
               lam = Lam ["X"] x
               tm = Cut (Application [x]) lam
           in stepTest "application 1" emptyEnv 1 tm (Right x)
         ]
       , testGroup "case"
           [ stepTest "case False of { False -> True; True -> False }"
               emptyEnv 1
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
             ty = Polytype [] (DataTy (UidTy boolId) [])
             -- TODO: remove shadowing
             tm = close1 "x" $ let_ "x" ty false (FV"x")
         in stepTest "let x = false in x" emptyEnv 1 tm (Right false)

       , let handler = forceTm [text|
               handle x : [e , <Abort>]Int with
                 Abort:
                   | <aborting -> k> -> one
                 | v -> two
             |]

             zero = mkForeignTm @Int intId [] 0
             one  = mkForeignTm @Int intId [] 1
             two  = mkForeignTm @Int intId [] 2

             resolutionState = uIdMapFromList $
               -- Provides Abort
               (Frank.resolvedDecls ^. globalCids) ++
               [("Int", intId)]

             Right handler' = resolveTm resolutionState handler
             handler'' = substitute "one" one $
               substitute "two" two
                 handler'

             handleVal = substitute "x" zero handler''

             abortCid = Frank.resolvedDecls ^?!
               globalCids . to HashMap.fromList . ix "Abort"
             abort = Command abortCid 0
             handleAbort = substitute "x" abort handler''
         in testGroup "handle"
              [ runTest "handle val" emptyEnv handleVal (Right two)
              , runTest "handle abort" emptyEnv handleAbort (Right one)
              ]

       , let
             ty = Polytype [] (DataTy (UidTy boolId) [])
             -- Just tm = cast [tmExp|
             --   let x: forall. bool = false in
             --     let y: forall. bool = not x in
             --       not y
             -- |]
             tm = close1 "x" $
                  let_ "x" ty false $
                    let_ "y" ty (Cut not (FV"x")) $
                      Cut not (FV"y")
         in stepTest "let x = false in let y = not x in not y"
              emptyEnv 3 tm (Right false)

       , let evenodd = forceTm [text|
               letrec
                 even : forall. Fix NatF -> Bool
                      = \n -> case unfix n of
                        NatF:
                          | <z>       -> <Bool.1> -- true
                          | <succ n'> -> odd n'
                 odd : forall. Fix NatF -> Bool
                     = \n -> case unfix n of
                       NatF:
                         | <z>       -> <Bool.0> -- false
                         | <succ n'> -> even n'
             |]

             evenodd' = resolveTm
               -- Provides NatF, Bool
               ((uIdMapFromList $ Frank.resolvedDecls ^. globalCids) <>
                (uIdMapFromList [("Fix", undefined)]))
               evenodd

             -- mkTm n = [| evenOdd n |]
             mkTm :: Int -> Tm Cid
             mkTm n = undefined

             natBoolEnv = emptyEnv
         in testGroup "letrec"
              [ stepTest "even 0"  natBoolEnv 1  (mkTm 0)  (Right true)
              , stepTest "even 7"  natBoolEnv 8  (mkTm 7)  (Right false)
              , stepTest "even 10" natBoolEnv 11 (mkTm 10) (Right true)
              , stepTest "odd 0"   natBoolEnv 1  (mkTm 0)  (Right false)
              , stepTest "odd 7"   natBoolEnv 8  (mkTm 7)  (Right true)
              , stepTest "odd 10"  natBoolEnv 11 (mkTm 10) (Right false)
              ]
       ]
