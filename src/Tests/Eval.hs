{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Tests.Eval where

import Bound -- (closed, abstract)
import Data.List (elemIndex)
import Network.IPLD as IPLD
import Test.Tasty
import Test.Tasty.HUnit

import Interplanetary.Eval
import Interplanetary.Parser.QQ
import Interplanetary.Predefined
import Interplanetary.Syntax
import Interplanetary.Util

stepTest
  :: String
  -> EvalEnv
  -> TmI
  -> Either Err TmI
  -> TestTree
stepTest name env tm expected = testCase name $
  runEvalM env (step tm) @?= expected

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
    , mkForeign @String "hello "
    , mkForeign @String "world"
    , mkForeign @String "hello world"
    ]
  )

-- TODO: can this not be a pattern synonym?
bool :: Int -> TmI
bool i = DataTm boolId i []

unitTests :: TestTree
unitTests =
  let one = mkForeignTm @Int 1
      zero = mkForeignTm @Int 0
      two = mkForeignTm @Int 2
      four = mkForeignTm @Int 4

      false = bool 0
      true = bool 1

      hello = mkForeignTm @String "hello "
      world = mkForeignTm @String "world"
      helloWorld = mkForeignTm @String "hello world"

      add = ForeignFunTm intOpsId 0
      sub = ForeignFunTm intOpsId 1
      cat = ForeignFunTm strOpsId 0

  in testGroup "evaluation"
       [ testGroup "foreign operations"
         [ stepTest "1 + 1" simpleEnv
           (Cut (Application [one, one]) add)
           (Right two)
         , stepTest "2 + 2" simpleEnv
           (Cut (Application [two, two]) add)
           (Right four)
         , stepTest "2 - 1" simpleEnv
           (Cut (Application [two, one]) sub)
           (Right one)
         , stepTest "\"hello \" <> \"world\"" simpleEnv
           (Cut (Application [hello, world]) cat)
           (Right helloWorld)
         ]
       , testGroup "functions"
         [ let Just tm = closeVar ("x", 0) [tmExp| (\y -> y) x |]
           in stepTest "application 1" simpleEnv tm (Right (V 0))
         ]
       , let casePiece =
               Case boolId
                 [ abstract (`elemIndex` []) one
                 , abstract (`elemIndex` []) zero
                 ]
         in testGroup "case"
              [ stepTest "case False of { False -> 0; True -> 1 }" simpleEnv
                (Cut casePiece false)
                (Right one)
              , stepTest "case True of { False -> 0; True -> 1 }" simpleEnv
                (Cut casePiece true)
                (Right zero)
              ]
       ]

closeVar :: Eq a => (a, b) -> Tm uid c a -> Maybe (Tm uid c b)
closeVar (a, b) = instantiate1 (V b) <$$> closed . abstract1 a

runEvalTests :: IO ()
runEvalTests = defaultMain unitTests
