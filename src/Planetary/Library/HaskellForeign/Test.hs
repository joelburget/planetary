{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Planetary.Library.HaskellForeign.Test where

import Control.Lens
import Data.Text (Text)
import Prelude hiding (not)
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Support.Ids
import Planetary.Library.HaskellForeign
import Planetary.Core.Eval.Test (stepTest)
import Planetary.Core.Typecheck.Test (checkTest, exampleTables, emptyTypingEnv)


-- TODO: this is awfully kludgy:
-- * ids are duplicated here and in Interplanetary.Ids
-- * we shouldn't need to supply the Uid separately -- it can be derived from
-- the data
simpleEnv :: EvalEnv
simpleEnv =
  ( haskellOracles
  , uIdMapFromList
    [ mkForeign @Int 1
    , mkForeign @Int 2
    , mkForeign @Int 4
    , mkForeign @Text "hello "
    , mkForeign @Text "world"
    , mkForeign @Text "hello world"
    ]
  )

unitTests :: TestTree
unitTests =
  let -- zero = mkForeignTm @Int 0
      one  = mkForeignTm @Int intId [] 1
      two  = mkForeignTm @Int intId [] 2
      four = mkForeignTm @Int intId [] 4

      hello = mkForeignTm @Text textId [] "hello "
      world = mkForeignTm @Text textId [] "world"
      helloWorld = mkForeignTm @Text textId [] "hello world"

      add spine = Cut (Application spine) (CommandV intOpsId 0)
      sub spine = Cut (Application spine) (CommandV intOpsId 1)
      cat spine = Cut (Application spine) (CommandV textOpsId 0)

      tables = exampleTables & _2 .~ interfaceTable

   in testGroup "haskell foreign"
       [ testGroup "evaluation"
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
         ]

       , testGroup "typechecking"
         [ checkTest "1 : Int" tables emptyTypingEnv one intTy
         , checkTest "1 + 1 : Int" tables emptyTypingEnv (add [one, one]) intTy
         , checkTest "\"hello \" <> \"world\" : String" tables emptyTypingEnv (cat [hello, world]) textTy
         , let tm = (add [one, hello])
               err = TyUnification textTy intTy
           in testCase "1 + \"hello\" /: Int" $
             runTcM tables emptyTypingEnv (check tm intTy) @?= Left err
         ]
       ]


runHaskellForeignTests :: IO ()
runHaskellForeignTests = defaultMain unitTests
