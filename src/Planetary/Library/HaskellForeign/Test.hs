{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Planetary.Library.HaskellForeign.Test where

import Control.Lens
import Data.Text (Text)
import NeatInterpolation
import Prelude hiding (not)
import Test.Tasty

import Planetary.Core
import Planetary.Library.HaskellForeign
import Planetary.Core.Eval.Test (stepTest)
import Planetary.Core.Typecheck.Test
  (checkTest, emptyTypingEnv, emptyTypingState)
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser

-- TODO: this is awfully kludgy:
-- * ids are duplicated here and in Interplanetary.Ids
-- * we shouldn't need to supply the Uid separately -- it can be derived from
-- the data
simpleEnv :: EvalEnv
simpleEnv = EvalEnv
  haskellOracles
  (uIdMapFromList
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

      env = emptyTypingEnv & typingInterfaces .~ interfaceTable

   in testGroup "haskell foreign" $
       [ testGroup "evaluation"
         [ stepTest "1 + 1" simpleEnv 1
           -- [tmExp| add one one |]
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
         [ checkTest "1 : Int" env emptyTypingState one intTy
         , checkTest "1 + 1 : Int" env emptyTypingState (add [one, one]) intTy
         , checkTest "\"hello \" <> \"world\" : String" env emptyTypingState (cat [hello, world]) textTy
         -- , let tm = add [one, hello]
         --       err = TyUnification textTy intTy

         --   -- TODO: checkFailTest?
         --   in testCase "1 + \"hello\" /: Int" $
         --     runTcM env emptyTypingState (check tm intTy) @?= Left err
         ]

       , testGroup "lfix" $
         let decls = forceDeclarations [text|
             data ListF a f =
               <nilf>
               | <consf a f>
             |]

             Right resolved = nameResolution decls mempty
             listFDecl = resolved ^. datatypes

             Just (listfId, _) = namedData "ListF" resolved

             lfixTm x   = DataTm lfixId 0 [x]
             lcons x xs = lfixTm (DataTm listfId 1 [x, xs])
             lnil       = lfixTm (DataTm listfId 0 [])

             lfixTy f     = DataTy lfixId [TyArgVal f]
             listfTy1 a   = DataTy listfId [TyArgVal a]
             listfTy2 a f = DataTy listfId [TyArgVal a, TyArgVal f]

             -- [1]
             oneList :: TmI
             oneList = lcons one lnil

             intListTy :: ValTyI
             intListTy = lfixTy (listfTy1 intTy)

             -- f = ListF a
             -- =>
             -- data FixListF a = Fix (ListF a (Fix (ListF a)))
             --
             -- Declare Fix @ListF
             -- a = VariableTy 0
             specialDecl = DataTypeInterface []
               [ ConstructorDecl
                   "FixListF"
                   -- [listfTy2 intTy intListTy]
                   [listfTy2 intTy (listfTy1 intTy)]
                   [TyArgVal intListTy]
               ]
             specialDecl' = uIdMapFromList [(lfixId, specialDecl)]

             dtypes =
               (haskellDataTypes `uidMapUnion` listFDecl `uidMapUnion` specialDecl')

             env' = emptyTypingEnv & typingData .~ dtypes

         in [ checkTest "ListF []" env' emptyTypingState lnil intListTy
            , checkTest "ListF [1]" env' emptyTypingState oneList intListTy
            ]
      ]


runHaskellForeignTests :: IO ()
runHaskellForeignTests = defaultMain unitTests
