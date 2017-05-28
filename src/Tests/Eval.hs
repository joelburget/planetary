{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Tests.Eval where

import Prelude hiding (not)
import Data.Text (Text)
import Network.IPLD as IPLD
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Library.HaskellForeign
import Planetary.Support.Parser.QQ
import Planetary.Support.UIds

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
  in testCase name $ fst (runEvalM env [] actual) @?= expected

mkForeign :: IsIpld a => a -> (Cid, IPLD.Value)
mkForeign val = let val' = toIpld val in (valueCid val', val')

mkForeignTm :: IsIpld a => a -> TmI
mkForeignTm = ForeignDataTm . fst . mkForeign

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
    , mkForeign @Text "hello "
    , mkForeign @Text "world"
    , mkForeign @Text "hello world"
    ]
  )

bool :: Int -> Tm Cid a b
bool i = DataTm boolId i []

unitTests :: TestTree
unitTests =
  let one = mkForeignTm @Int 1
      zero = mkForeignTm @Int 0
      two = mkForeignTm @Int 2
      four = mkForeignTm @Int 4

      hello = mkForeignTm @Text "hello "
      world = mkForeignTm @Text "world"
      helloWorld = mkForeignTm @Text "hello world"

      add = CommandV intOpsId 0
      sub = CommandV intOpsId 1
      cat = CommandV strOpsId 0

      -- true, false :: forall a b. Tm Cid a b
      false = bool 0
      true = bool 1

      not = Case boolId
        [ ([], abstract0 true)
        , ([], abstract0 false)
        ]
      boolOfInt = Case boolId
        [ ([], abstract0 one)
        , ([], abstract0 zero)
        ]

  in testGroup "evaluation"
       [ testGroup "foreign operations"
         [ stepTest "1 + 1" simpleEnv 1
           -- [tmExp| $add $one $one |]
           (add [one, one])
           (Right two)
         , stepTest "2 + 2" simpleEnv 1
           (add [two, two])
           (Right four)
         , stepTest "2 - 1" simpleEnv 1
           (sub [two, one])
           (Right one)
         , stepTest "\"hello \" <> \"world\"" simpleEnv 1
           (cat [hello, world])
           (Right helloWorld)
         , stepTest "not false" simpleEnv 1
           (Cut not false)
           (Right true)
         ]
       , testGroup "functions"
         [ let x = V 0
               tm = [tmExp| (\y -> y) $x |]
           in stepTest "application 1" simpleEnv 1 tm (Right x)
         ]
       , testGroup "case"
           [ stepTest "case False of { False -> 0; True -> 1 }" simpleEnv 1
             -- [tmExp|
             --   case $false of
             --     $boolId:
             --       | -> $one
             --       | -> $zero
             -- |]
             (Cut boolOfInt false)
             (Right one)
           , stepTest "case True of { False -> 0; True -> 1 }" simpleEnv 1
             (Cut boolOfInt true)
             (Right zero)
           ]
       , let ty = PolytypeP [] (DataTy boolId [])
             -- TODO: remove shadowing
             Just tm = closeVar ("x", 0) $ let_ "x" ty false (V"x")
         in stepTest "let x = false in x" simpleEnv 1 tm (Right false)

       , let
             ty = PolytypeP [] (DataTy boolId [])
             -- Just tm = cast [tmExp|
             --   let x: forall. $boolId = $false in
             --     let y: forall. $boolId = $not x in
             --       $not y
             -- |]
             Just tm = closeVar ("x", 0) $
                  let_ "x" ty false $
                    let_ "y" ty (Cut not (V"x")) $
                      Cut not (V"y")
         in stepTest "let x = false in let y = not x in not y"
              simpleEnv 3 tm (Right false)

       -- , let
       --   in stepTest ""
       ]

runEvalTests :: IO ()
runEvalTests = defaultMain unitTests
