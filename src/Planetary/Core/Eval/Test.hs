{-# language DataKinds #-}
{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Core.Eval.Test (unitTests, stepTest, runTest) where

import Control.Arrow (right)
import Control.Lens
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import NeatInterpolation
import Network.IPLD as IPLD
import Prelude hiding (not)
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Support.Ids hiding (boolId) -- XXX fix this
import Planetary.Support.NameResolution (resolveTm, closeTm)
import Planetary.Support.Parser (forceTm)
import qualified Planetary.Library.FrankExamples as Frank
import Planetary.Library.HaskellForeign (mkForeignTm, haskellOracles)
import qualified Planetary.Library.HaskellForeign as HaskellForeign
import Planetary.Util (Stack)

import Debug.Trace

mkEmptyState :: TmI -> EvalState
mkEmptyState tm = EvalState tm [] [] Nothing

stepTest
  :: String
  -> AmbientEnv
  -> Int
  -> TmI
  -> Either Err TmI
  -> TestTree
stepTest name env steps tm expected =
  let applications :: [EvalM EvalState]
      applications = iterate (step =<<) (pure (mkEmptyState tm))
      actual = applications !! steps

  in testCase name $ do
    result <- runEvalM env actual

    let result' = fst result
        result'' = right _evalFocus result'

    result'' @?= expected

runTest
  :: String
  -> AmbientEnv
  -> TmI
  -> Either Err TmI
  -> TestTree
runTest name env tm expected = testCase name $ do
  result <- run env (mkEmptyState tm)
  fst result @?= expected

boolId :: Cid
Just (boolId, _) = namedData "Bool" Frank.resolvedDecls

bool :: Int -> Tm Cid
bool i = DataConstructor boolId i []

unitTests :: TestTree
unitTests  =
  let emptyEnv :: AmbientEnv
      emptyEnv = AmbientEnv mempty mempty

      -- true, false :: forall a b. Tm Cid a b
      false = bool 0
      true = bool 1

      not tm = CaseP boolId tm
        [ ([], true)
        , ([], false)
        ]
      -- boolOfInt = Case boolId
      --   [ ([], one)
      --   , ([], zero)
      --   ]

  in testGroup "evaluation"
       {-
       [ let x = BV 0 0
             -- tm = forceTm "(\y -> y) x"
             lam = Lam ["X"] x
         in testGroup "functions"
            [ stepTest "application 1" emptyEnv 1 (AppN lam [x]) (Right x)
            , stepTest "application 2" emptyEnv 1
              (AppT lam [x])
              (Right x)
            -- TODO: test further steps with bound variables
            ]

       , testGroup "case"
           [ stepTest "case False of { False -> True; True -> False }"
               emptyEnv 1
               (not false)
               (Right true)
           , stepTest "case True of { False -> True; True -> False }"
               emptyEnv 1
               (not true)
               (Right false)

           , stepTest "not false" emptyEnv 1
             (not false)
             (Right true)
           ]

       , let ty :: Polytype Cid
             ty = Polytype [] (DataTy (UidTy boolId) [])
             -- TODO: remove shadowing
             tm = close1 "x" $ let_ "x" ty false (FV"x")
         in testGroup "let"
            [ stepTest "let x = false in x" emptyEnv 1 tm
              (Right false)
            , stepTest "let x = false in x" emptyEnv 2 tm
              (Right false)
            ]

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
              -- [ runTest "handle val" emptyEnv handleVal (Right two)
              [ runTest "handle abort" emptyEnv handleAbort (Right one)
              -- XXX test continuing from handler
              ]

--        , let
--              ty = Polytype [] (DataTy (UidTy boolId) [])
--              tm = close1 "x" $
--                   let_ "x" ty false $
--                     let_ "y" ty (not (FV"x")) $
--                       not (FV"y")

--              -- both versions of tm should be equivalent
--              resolutionState = todo "resolutionState"
--              Right tm2 = resolveTm resolutionState $ forceTm [text|
--                let x: forall. Bool = false in
--                  let y: forall. Bool = not x in
--                    not y
--              |]

--          in testGroup "let x = false in let y = not x in not y"
--               [ stepTest "tm"  emptyEnv 12 tm  (Right false)
--               -- , stepTest "tm2" emptyEnv 3 tm2 (Right false)
--               ]
-}

       [ let evenodd = forceTm [text|
               letrec
                 even : forall. {<Fix NatF> -> <Bool>}
                      = \n -> case n of
                        NatF:
                          | <z>       -> <Bool.1> -- true
                          | <succ n'> -> odd n'
                 odd : forall. {<Fix NatF> -> <Bool>}
                     = \m -> case m of
                       NatF:
                         | <z>       -> <Bool.0> -- false
                         | <succ m'> -> even m'
               in body
             |]

             Right evenodd' = resolveTm
               -- Provides NatF, Bool
               (fromList (Frank.resolvedDecls ^. globalCids) <>
                [("Fix", lfixId)])
               evenodd

             -- mkFix = Command fixOpsId 0
             -- unFix = Command fixOpsId 1
             Just (natfId, _) = namedData "NatF" Frank.resolvedDecls
             Just (_, fixDecl) = namedInterface "FixOps" HaskellForeign.resolvedDecls
             EffectInterface fixBinders fixCtrs = fixDecl

             [_, CommandDeclaration _ _ unfixResult] = fixCtrs
             unfixTy = Polytype fixBinders unfixResult

             -- mkTm n = [| evenOdd n |]
             mkTm :: Text -> Int -> Tm Cid
             mkTm fnName n =
               let mkNat 0 = DataConstructor natfId 0 []
                   mkNat k = DataConstructor natfId 1 [mkNat (k - 1)]

                   Right tm = closeTm $
                     -- substitute "unFix" unFix $
                       substitute "body"
                         (AppT (FV fnName) [mkNat n])
                         evenodd'
               in tm

             natBoolEnv = AmbientEnv haskellOracles []
         in testGroup "letrec"
              [ stepTest "even 0"  natBoolEnv 4  (traceShowId $ mkTm "even" 0)  (Right true)
              -- [ stepTest "odd 0"   natBoolEnv 16  (mkTm "odd"  0)  (Right false)
              -- [ stepTest "even 3"  natBoolEnv 31 (traceShowId $ mkTm "even" 1)  (Right false)
              -- [ stepTest "even 3"  natBoolEnv 7 (traceShowId $ mkTm "even" 2)  (Right true)
              -- , stepTest "even 7"  natBoolEnv 8  (mkTm "even" 7)  (Right false)
              -- , stepTest "even 10" natBoolEnv 11 (mkTm "even" 10) (Right true)
              -- , stepTest "odd 7"   natBoolEnv 8  (mkTm "odd"  7)  (Right true)
              -- , stepTest "odd 10"  natBoolEnv 11 (mkTm "odd"  10) (Right false)
              ]
       ]
