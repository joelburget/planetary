{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Tests.Eval where

import Prelude hiding (not)
import Bound -- (closed, abstract)
import Data.Hashable (Hashable)
import qualified Data.HashMap.Strict as HashMap
import Network.IPLD as IPLD
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Library.HaskellForeign
import Planetary.Support.Parser.QQ
import Planetary.Support.UIds
import Planetary.Util

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

      not = Case boolId
        [ abstract0 true
        , abstract0 false
        ]
      boolOfInt = Case boolId
        [ abstract0 one
        , abstract0 zero
        ]

  in testGroup "evaluation"
       [ testGroup "foreign operations"
         [ stepTest "1 + 1" simpleEnv 1
           (Cut (Application [one, one]) add)
           (Right two)
         , stepTest "2 + 2" simpleEnv 1
           (Cut (Application [two, two]) add)
           (Right four)
         , stepTest "2 - 1" simpleEnv 1
           (Cut (Application [two, one]) sub)
           (Right one)
         , stepTest "\"hello \" <> \"world\"" simpleEnv 1
           (Cut (Application [hello, world]) cat)
           (Right helloWorld)
         , stepTest "not false" simpleEnv 1
           (Cut not false)
           (Right true)
         ]
       , testGroup "functions"
         [ let Just tm = closeVar ("x", 0) [tmExp| (\y -> y) x |]
           in stepTest "application 1" simpleEnv 1 tm (Right (V 0))
         ]
       , testGroup "case"
           [ stepTest "case False of { False -> 0; True -> 1 }" simpleEnv 1
             (Cut boolOfInt false)
             (Right one)
           , stepTest "case True of { False -> 0; True -> 1 }" simpleEnv 1
             (Cut boolOfInt true)
             (Right zero)
           ]
       , let ty = polytype [] (DataTy boolId [])
             -- TODO: remove shadowing
             false = DataTm boolId 0 []
             Just tm = closeVar ("x", 0) $ let_ "x" ty false (V"x")
         in stepTest "let x = false in x" simpleEnv 1 tm (Right false)

       , let
             ty = polytype [] (DataTy boolId [])
             false = DataTm boolId 0 []
             true = DataTm boolId 1 []
             not :: Continuation Cid Int String
             not = Case boolId
               [ abstract0 (trace "forcing true" true)
               , abstract0 (trace "forcing false" false)
               ]
             Just tm = closeVar ("x", 0) $
                  let_ "x" ty false $
                    let_ "y" ty (Cut not (V"x")) $
                      (Cut not (V"y"))
         in stepTest "let x = false in let y = not x in not y"
              simpleEnv 3 tm (Right false)
       ]

-- | abstract 0 variables
abstract0 :: Monad f => f a -> Scope b f a
abstract0 = abstract (error "abstract0")

closeVar :: Eq a => (a, b) -> Tm uid c a -> Maybe (Tm uid c b)
closeVar (a, b) = instantiate1 (V b) <$$> closed . abstract1 a

closeVars :: (Eq a, Hashable a) => [(a, b)] -> Tm uid c a -> Maybe (Tm uid c b)
closeVars vars =
  let mapping = HashMap.fromList vars
      abstractor k = HashMap.lookup k mapping
  in instantiate V <$$> closed . abstract abstractor

runEvalTests :: IO ()
runEvalTests = defaultMain unitTests
