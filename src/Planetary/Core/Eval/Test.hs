{-# language DataKinds #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Core.Eval.Test (unitTests, stepTest) where

import Control.Lens
import qualified Data.HashMap.Strict as HashMap
import Data.Monoid ((<>))
import Data.Text (Text)
import NeatInterpolation
import Network.IPLD as IPLD
import Prelude hiding (not)
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Support.Ids
import Planetary.Support.NameResolution (resolveTm)
import Planetary.Support.Parser (forceTm)
import qualified Planetary.Library.FrankExamples as Frank
import Planetary.Library.HaskellForeign (mkForeignTm, boolTy)
import qualified Planetary.Library.HaskellForeign as HaskellForeign
import Planetary.Util (todo)

import Debug.Trace

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

             resolutionState = fromList $
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
             tm = close1 "x" $
                  let_ "x" ty false $
                    let_ "y" ty (Cut not (FV"x")) $
                      Cut not (FV"y")

             -- both versions of tm should be equivalent
             resolutionState = todo "resolutionState"
             Right tm2 = resolveTm resolutionState $ forceTm [text|
               let x: forall. Bool = false in
                 let y: forall. Bool = not x in
                   not y
             |]

         in testGroup "let x = false in let y = not x in not y"
              [ stepTest "tm"  emptyEnv 3 tm  (Right false)
              , stepTest "tm2" emptyEnv 3 tm2 (Right false)
              ]

       , let evenodd = forceTm [text|
               letrec
                 even : forall. {<Fix NatF> -> <Bool>}
                      = \n -> case unFix n of
                        NatF:
                          | <z>       -> <Bool.1> -- true
                          | <succ n'> -> odd n'
                 odd : forall. {<Fix NatF> -> <Bool>}
                     = \n -> case unFix n of
                       NatF:
                         | <z>       -> <Bool.0> -- false
                         | <succ n'> -> even n'
               in body
             |]

             Right evenodd' = resolveTm
               -- Provides NatF, Bool
               ((fromList $ Frank.resolvedDecls ^. globalCids) <>
                [("Fix", lfixId)])
               evenodd

             mkFix = Command fixOpsId 0
             unFix = Command fixOpsId 1
             Just (natfId, _) = namedData "NatF" Frank.resolvedDecls
             Just (_, fixDecl) = namedInterface "FixOps" HaskellForeign.resolvedDecls
             EffectInterface fixBinders fixCtrs = fixDecl

             [_, CommandDeclaration _ _ unfixResult] = fixCtrs
             unfixTy = Polytype fixBinders unfixResult

             -- mkTm n = [| evenOdd n |]
             mkTm :: Text -> Int -> Tm Cid
             mkTm fnName n =
               let mkNat 0 = Cut mkFix (Application [DataConstructor natfId 0 []])
                   mkNat k = Cut mkFix (Application [DataConstructor natfId 1 [mkNat (k - 1)]])

               in let_ "unFix" unfixTy unFix $
                    -- closeXXX fnName $
                      let_ "body" (Polytype [] boolTy)
                        (Cut (FV fnName) (Application [mkNat n]))
                        evenodd'

             natBoolEnv = emptyEnv
         in testGroup "letrec"
              [ stepTest "even 0"  natBoolEnv 2  (mkTm "even" 0)  (Right true)
              -- , stepTest "even 7"  natBoolEnv 8  (mkTm "even" 7)  (Right false)
              -- , stepTest "even 10" natBoolEnv 11 (mkTm "even" 10) (Right true)
              -- , stepTest "odd 0"   natBoolEnv 1  (mkTm "odd"  0)  (Right false)
              -- , stepTest "odd 7"   natBoolEnv 8  (mkTm "odd"  7)  (Right true)
              -- , stepTest "odd 10"  natBoolEnv 11 (mkTm "odd"  10) (Right false)
              ]
       ]
