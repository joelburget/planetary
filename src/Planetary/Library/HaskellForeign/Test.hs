{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Library.HaskellForeign.Test (unitTests) where

import Control.Lens
import Control.Unification (unfreeze)
import Data.Monoid ((<>))
import Data.Text (Text)
import NeatInterpolation
import Prelude hiding (not)
import Test.Tasty

import Planetary.Core
import Planetary.Library.HaskellForeign
import Planetary.Core.Eval.Test (stepTest)
import Planetary.Core.Typecheck.Test (checkTest, emptyTypingEnv)
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser

-- TODO: this is awfully kludgy:
-- * ids are duplicated here and in Interplanetary.Ids
-- * we shouldn't need to supply the Uid separately -- it can be derived from
-- the data
simpleEnv :: AmbientEnv
simpleEnv = AmbientEnv
  haskellOracles
  [ mkForeign @Int 1
  , mkForeign @Int 2
  , mkForeign @Int 4
  , mkForeign @Text "hello "
  , mkForeign @Text "world"
  , mkForeign @Text "hello world"
  ]

unitTests :: TestTree
unitTests =
  let -- zero = mkForeignTm @Int 0
      one  = mkForeignTm @Int intId [] 1
      two  = mkForeignTm @Int intId [] 2
      four = mkForeignTm @Int intId [] 4

      hello = mkForeignTm @Text textId [] "hello "
      world = mkForeignTm @Text textId [] "world"
      helloWorld = mkForeignTm @Text textId [] "hello world"

      add = AppN (Command intOpsId 0)
      sub = AppN (Command intOpsId 1)
      cat = AppN (Command textOpsId 0)

      env = emptyTypingEnv & typingInterfaces .~ interfaceTable

   in testGroup "haskell foreign"
       [ testGroup "evaluation"
         [ stepTest "1 + 1" simpleEnv 3
           -- [tmExp| add one one |]
           (add [one, one])
           (Right two)
         , stepTest "2 + 2" simpleEnv 2
           (add [two, two])
           (Right four)
         , stepTest "2 - 1" simpleEnv 2
           (sub [two, one])
           (Right one)
         , stepTest "\"hello \" <> \"world\"" simpleEnv 2
           (cat [hello, world])
           (Right helloWorld)
         ]

       , testGroup "typechecking"
         [ checkTest "1 : Int" env one (unfreeze intTy)
         , checkTest "1 + 1 : Int" env (add [one, one]) (unfreeze intTy)
         , checkTest "\"hello \" <> \"world\" : String" env (cat [hello, world]) (unfreeze textTy)
         -- , let tm = add [one, hello]
         --       err = TyUnification textTy intTy

         --   -- TODO: checkFailTest?
         --   in testCase "1 + \"hello\" /: Int" $
         --     runTcM env (check tm intTy) @?= Left err
         ]

       , testGroup "lfix" $
         let decls = forceDeclarations [text|
             data ListF a f =
               | <nilf>
               | <consf a f>
             |]

             Right resolved = resolveDecls mempty decls
             listFDecl = resolved ^. datatypes

             Just (listfId, _) = namedData "ListF" resolved

             lfixTm x   = DataConstructor lfixId 0 [x]
             lcons x xs = lfixTm (DataConstructor listfId 1 [x, xs])
             lnil       = lfixTm (DataConstructor listfId 0 [])

             lfixTy f     = DataTy (UidTy lfixId) [TyArgVal f]
             listfTy1 a   = DataTy (UidTy listfId) [TyArgVal a]
             listfTy2 a f = DataTy (UidTy listfId) [TyArgVal a, TyArgVal f]

             -- [1]
             oneList :: TmI
             oneList = lcons one lnil

             listTy :: ValTyI -> ValTyI
             listTy a = lfixTy (listfTy1 a)

             intListTy :: ValTyI
             intListTy = listTy intTy

             -- f = ListF a
             -- =>
             -- data FixListF a = Fix (ListF a (Fix (ListF a)))
             specialDecl = DataTypeInterface []
               [ ConstructorDecl
                   "FixListF"
                   [listfTy2 intTy intListTy]
                   [TyArgVal (listfTy1 intTy)]
               ]
             specialDecl' = [(lfixId, specialDecl)]

             dtypes = {-haskellDataTypes <>-} listFDecl <> specialDecl'

             env' = emptyTypingEnv & typingData .~ dtypes

         in [ checkTest "ListF []" env' lnil (unfreeze intListTy)
            , checkTest "ListF [1]" env' oneList (unfreeze intListTy)
            ]
      ]
