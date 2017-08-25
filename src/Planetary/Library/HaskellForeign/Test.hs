{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Library.HaskellForeign.Test (unitTests) where

import Control.Lens
import Control.Unification (unfreeze)
import Data.Semigroup ((<>))
import Data.Text (Text)
import NeatInterpolation
import Prelude hiding (not)
import EasyTest

import Planetary.Core
import Planetary.Library.HaskellForeign
import Planetary.Core.Eval.Test (runTest)
import Planetary.Core.Typecheck.Test (checkTest, emptyTypingEnv)
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser

store :: ValueStore
store =
  [ mkForeign @Int 1
  , mkForeign @Int 2
  , mkForeign @Int 4
  , mkForeign @Text "hello "
  , mkForeign @Text "world"
  , mkForeign @Text "hello world"
  ]

unitTests :: Test ()
unitTests =
  let -- zero = mkForeignTm @Int 0
      one  = mkForeignTm @Int intId [] 1
      two  = mkForeignTm @Int intId [] 2
      four = mkForeignTm @Int intId [] 4

      oneV  = mkForeignVal @Int intId [] 1
      twoV  = mkForeignVal @Int intId [] 2
      fourV = mkForeignVal @Int intId [] 4

      hello = mkForeignTm @Text textId [] "hello "
      world = mkForeignTm @Text textId [] "world"
      helloWorld = mkForeignVal @Text textId [] "hello world"

      add = AppN (Command intOpsId 0)
      sub = AppN (Command intOpsId 1)
      cat = AppN (Command textOpsId 0)

      env = emptyTypingEnv & typingInterfaces .~ interfaceTable

      simpleEnvRunTest desc
        = runTest desc (AmbientHandlers haskellOracles) store

   in scope "haskell foreign" $ tests
       [ scope "evaluation" $ tests
         [ simpleEnvRunTest "1 + 1"
           -- [tmExp| add one one |]
           (add [one, one])
           (Right twoV)
         , simpleEnvRunTest "2 + 2"
           (add [two, two])
           (Right fourV)
         , simpleEnvRunTest "2 - 1"
           (sub [two, one])
           (Right oneV)
         , simpleEnvRunTest "\"hello \" <> \"world\""
           (cat [hello, world])
           (Right helloWorld)
         ]

       , scope "typechecking" $ tests
         [ checkTest "1 : Int" env one (unfreeze intTy)
         , checkTest "1 + 1 : Int" env (add [one, one]) (unfreeze intTy)
         , checkTest "\"hello \" <> \"world\" : Text" env
           (cat [hello, world])
           (unfreeze textTy)
         -- , let tm = add [one, hello]
         --       err = TyUnification textTy intTy

         --   -- TODO: checkFailTest?
         --   in testCase "1 + \"hello\" /: Int" $
         --     runTcM env (check tm intTy) @?= Left err
         ]

       , scope "lfix" $
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

         in tests
            [ checkTest "ListF []" env' lnil (unfreeze intListTy)
            , checkTest "ListF [1]" env' oneList (unfreeze intListTy)
            ]
      ]
