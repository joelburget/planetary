{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Planetary.Library.HaskellForeign.Test where

import Data.Text (Text)
import Prelude hiding (not)
import Network.IPLD as IPLD
import Test.Tasty

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
      one  = mkForeignTm @Int 1
      two  = mkForeignTm @Int 2
      four = mkForeignTm @Int 4

      hello = mkForeignTm @Text "hello "
      world = mkForeignTm @Text "world"
      helloWorld = mkForeignTm @Text "hello world"

      add = CommandV intOpsId 0
      sub = CommandV intOpsId 1
      cat = CommandV strOpsId 0

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
         [ checkTest "1 : Int" exampleTables emptyTypingEnv one intTy
         ]
       ]


runHaskellForeignTests :: IO ()
runHaskellForeignTests = defaultMain unitTests
