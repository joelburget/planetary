{-# language FlexibleContexts #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeFamilies #-}
module Planetary.Core.Typecheck.Test
  ( unitTests
  , checkTest
  , emptyTypingEnv
  ) where

import Control.Lens
import Control.Unification (freeze, unfreeze)
import Control.Unification.IntVar
import Data.ByteString (ByteString)
import Data.Text (Text)
import NeatInterpolation
import Network.IPLD
import EasyTest

import Planetary.Core
import Planetary.Library
import Planetary.Library.HaskellForeign (intTy, boolTy)
import Planetary.Library.FrankExamples as Frank
import Planetary.Support.NameResolution
import Planetary.Support.Parser

checkTest
  :: Text
  -> TypingEnvI
  -> TmI
  -> UTy IntVar
  -> Test ()
checkTest name tables tm ty = scope name $ case runTcM tables (check tm ty) of
  Right () -> ok
  other -> fail (show other)

inferTest
  :: Text
  -> TypingEnvI
  -> TmI
  -> Either TcErr (UTy IntVar)
  -> Test ()
inferTest name tables tm expected = scope name $ expectEq
  (freeze <$> runTcM tables (infer tm))
  (freeze <$> expected)

exampleInterfaces :: InterfaceTableI
exampleInterfaces = mempty

dataTypeTable :: DataTypeTableI
dataTypeTable = mempty

ambientAbility :: UTy IntVar
ambientAbility = unfreeze emptyAbility

emptyTypingEnv :: TypingEnvI
emptyTypingEnv = TypingEnv dataTypeTable exampleInterfaces ambientAbility []

mockCid :: ByteString -> Cid
mockCid = mkCid

unitTests :: Test ()
unitTests = scope "typechecking" $ tests
  [ scope "infer variable" $ tests
    [ let ty = VariableTyU "hippo"
          env = emptyTypingEnv & varTypes .~ [("x", Left ty)]
      in inferTest "VAR 1" env (V"x") (Right ty)
    , inferTest "VAR 2" emptyTypingEnv (V"x") (Left (LookupVarTy "x"))
    ]

  , scope "TODO: infer polyvar" $ tests
    [
    ]

  , scope "infer command" $ tests
    [ let domTy = DataTy (UidTy (mockCid "domain")) []
          codomTy = DataTy (UidTy (mockCid "codomain")) []
          cmdUid = mockCid "fire missiles"

          -- TODO: this duplication between ambient and interfaces is so bad
          cmdIfaces =
            [ (cmdUid, EffectInterface []
                [CommandDeclaration "fire missiles" [domTy] codomTy]
              )
            ]

          ambient = extendAbility emptyAbility $ Adjustment
            [ (cmdUid, [TyArgVal domTy])
            -- TODO: what does it mean to have an ability here?
            -- [ (cmdUid, [TyArgVal domTy, TyArgAbility _])
            ]

          tables = emptyTypingEnv & typingInterfaces .~ cmdIfaces
                                  & typingAbilities .~ unfreeze ambient

          cmd = Command cmdUid 0

          expected = Right $ unfreeze $
            SuspendedTy $ CompTy [domTy] $ Peg ambient codomTy

      in inferTest "COMMAND" tables cmd expected
    ]

  , let dataUid = mockCid "dataUid"
        v1Id = mockCid "v1"
        v2Id = mockCid "v2"
        tm1 = DataConstructor v1Id 0 []
        tm2 = DataConstructor v2Id 0 []
        ty1, ty2 :: TyFix'
        ty1 = DataTy (UidTy v1Id) []
        ty2 = DataTy (UidTy v2Id) []
        ty1ty2vals = [TyArgVal ty1, TyArgVal ty2]
        constr1 = ConstructorDecl "constr1" [ty1, ty2]
        constr2 = ConstructorDecl "constr2" []

        app fun = AppT fun [tm1, tm2]
        f = Lambda ["x", "y"] $ DataConstructor dataUid 0 [V"x", V"y"]
        resultTy = DataTy (UidTy dataUid) ty1ty2vals

        goodAnnF = Annotation f $ SuspendedTy $
          CompTy [ty1, ty2] (Peg emptyAbility resultTy)
        expected = Right (unfreeze resultTy)

        baddAnnF = Annotation f $ SuspendedTy $
          CompTy [ty1, ty1] (Peg emptyAbility resultTy)

        ty1Thawed = DataTy_ (unfreeze (UidTy v1Id)) []
        ty2Thawed = DataTy_ (unfreeze (UidTy v2Id)) []
        expectedBad = Left (MismatchFailure ty1Thawed ty2Thawed)

        tables = emptyTypingEnv & typingData .~
          [ (dataUid, DataTypeInterface [] [constr1 ty1ty2vals])
          , (v1Id, DataTypeInterface [] [constr2 []])
          , (v2Id, DataTypeInterface [] [constr2 []])
          ]

    in scope "sharing data defns" $ tests
         [ scope "infer app" $ tests
           [ inferTest "APP (1)" tables (app goodAnnF) expected
           , inferTest "APP (2)" tables (app baddAnnF) expectedBad
           ]
         , scope "check data" $ tests
           [ let tables' = emptyTypingEnv & typingData .~
                   [ (v1Id, DataTypeInterface [] [ConstructorDecl "constr" [] []]) ]
             in checkTest "DATA (simple)" tables' tm1 (unfreeze ty1)
           , let tm = DataConstructor dataUid 0 [tm1, tm2]
                 expectedTy = DataTy (UidTy dataUid) ty1ty2vals
             in checkTest "DATA (args)" tables tm (unfreeze expectedTy)
           ]
         ]

  , scope "infer annotation" $ tests
    [ let cid = mockCid "ty"
          ty = DataTy (UidTy cid) []
          tm = Annotation (DataConstructor cid 0 []) ty
          env = emptyTypingEnv & typingData .~
            [ (cid, DataTypeInterface []
              [ ConstructorDecl "constr" [] []
              ])
            ]
      in inferTest "COERCE" env tm (Right (unfreeze ty))
    ]

  , scope "TODO: check lambda" $ tests []

    , scope "case" $ tests
      [ do let abcdUid = mockCid "abcd"
               defgUid = mockCid "123424321432"
               abcdTy = DataTy (UidTy abcdUid) []
               abcdVal = DataConstructor abcdUid 0 []
               val = Annotation
                 (DataConstructor defgUid 1 [abcdVal, abcdVal])
                 (DataTy (UidTy defgUid) [])
               resolutionState =
                 [ ("abcd", abcdUid)
                 , ("defg", defgUid)
                 ]
           Right tm <- pure $ resolveTm resolutionState $ forceTm [text|
              case val of
                | <_ x y z> -> x
                | <_ y z> -> z
            |]
           let tm' = substitute "val" val tm
               -- decls = forceDeclarations [text|
               --     data abcd =
               --       | <abcd>
               --     data defg =
               --       | <defg1 abcd abcd abcd>
               --       | <defg2 abcd abcd>
               --   |]
               env = emptyTypingEnv & typingData .~
                 [ (abcdUid, DataTypeInterface []
                   [ ConstructorDecl "abcd" [] []
                   ])
                 , (defgUid, DataTypeInterface []
                   [ ConstructorDecl "defg1" [abcdTy, abcdTy, abcdTy] []
                   , ConstructorDecl "defg2" [abcdTy, abcdTy]         []
                   ])
                 ]
               expectedTy = unfreeze abcdTy
           checkTest "CASE" env tm' expectedTy
      ]

    , scope "check switch" $ tests
      [ let tm = V"x"
            dataUid = mockCid "dataUid"
            dataTy = unfreeze $ DataTy (UidTy dataUid) []
            expectedTy = dataTy
            env = emptyTypingEnv & varTypes .~ [("x", Left dataTy)]
        in checkTest "SWITCH" env tm expectedTy
      ]

    , scope "check handle" $ tests

        -- both branches should give us a bool
        [ do Right tm <- pure $ resolve $
                forceTm [text|
                  handle abort! : [e , <Abort>]Int with
                    Abort:
                      | <aborting -> k> -> x1
                    | v -> x2
                |]
             Just abortId <- pure $ Frank.resolvedDecls
                ^? globalCids
                 . ix "Abort"
             let abortAbility = Ability OpenAbility [(abortId, [])]
                 abortTy = SuspendedTy
                   (CompTy []
                     (Peg abortAbility intTy)) -- XXX generalize
                 env = emptyTypingEnv
                   & typingInterfaces .~ (Frank.resolvedDecls ^. interfaces)
                   & varTypes .~ (Left . unfreeze <$>
                     [ ("abort", abortTy)
                     , ("x1", boolTy)
                     , ("x2", boolTy)
                     ])
                   -- & varTypes .~ [Left . unfreeze <$> [abortTy, boolTy, boolTy]]
                 expectedTy = unfreeze boolTy
             checkTest "HANDLE (abort)" env tm expectedTy

        , do Right tm <- pure $ resolve $
                  forceTm [text|
                    handle val : [e, <Send Bool>, <Receive Bool>]Int with
                      Send Bool:
                        | <send y -> s> -> x1
                      Receive Bool:
                        | <receive -> r> -> x2
                      | v -> x3
                  |]
             let env = emptyTypingEnv
                   & typingInterfaces .~ (Frank.resolvedDecls ^. interfaces)
                   & varTypes .~ (Left . unfreeze <$>
                     [ ("val", intTy)
                     , ("x1", boolTy)
                     , ("x2", boolTy)
                     , ("x3", boolTy)
                     ])
                   -- & varTypes .~ [Left . unfreeze <$> [intTy, boolTy, boolTy, boolTy]]
                 expectedTy = unfreeze boolTy
             checkTest "HANDLE (multi)" env tm expectedTy
        ]

    , let
      in scope "polyvar instantiation" $ tests
        [
        ]

  ]
