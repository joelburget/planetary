{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
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
import qualified Data.HashMap.Strict as HashMap
import NeatInterpolation
import Network.IPLD
import EasyTest

import Planetary.Core
import Planetary.Library.HaskellForeign (intTy, boolTy)
import Planetary.Library.FrankExamples as Frank
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser

checkTest
  :: String
  -> TypingEnvI
  -> TmI
  -> UTy IntVar
  -> Test ()
checkTest name tables tm ty = scope name $ case runTcM tables (check tm ty) of
  Right () -> ok
  other -> fail (show other)

inferTest
  :: String
  -> TypingEnvI
  -> TmI
  -> Either TcErr (UTy IntVar)
  -> Test ()
inferTest name tables tm expected = scope name $ expect $
  (freeze <$> runTcM tables (infer tm)) == (freeze <$> expected)

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
    [ let ty = FreeVariableTyU "hippo"
          env = emptyTypingEnv & varTypes .~ [[Left ty]]
      in inferTest "VAR 1" env (BV 0 0) (Right ty)
    , inferTest "VAR 2" emptyTypingEnv (BV 0 0) (Left (LookupVarTy 0 0))
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
        ty1 = DataTy (UidTy v1Id) []
        ty2 = DataTy (UidTy v2Id) []
        ty1ty2vals = [TyArgVal ty1, TyArgVal ty2]
        constr1 = ConstructorDecl "constr1" [ty1, ty2]
        constr2 = ConstructorDecl "constr2" []

        app f = AppT f [tm1, tm2]
        f = Lam ["x", "y"] $ DataConstructor dataUid 0 [FV"x", FV"y"]
        resultTy = DataTy (UidTy dataUid) ty1ty2vals

        goodAnnF = Annotation f $ SuspendedTy $
          CompTy [ty1, ty2] (Peg emptyAbility resultTy)
        expected = Right (unfreeze resultTy)

        baddAnnF = Annotation f $ SuspendedTy $
          CompTy [ty1, ty1] (Peg emptyAbility resultTy)
        expectedBad = Left (MismatchFailure undefined undefined)

        tables = emptyTypingEnv & typingData .~
          [ (dataUid, DataTypeInterface [] [constr1 ty1ty2vals])
          , (v1Id, DataTypeInterface [] [constr2 []])
          , (v2Id, DataTypeInterface [] [constr2 []])
          ]

    in scope "(sharing data defns)" $ tests
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
      [ let abcdUid = mockCid "abcd"
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
            Right tm = resolveTm resolutionState $ forceTm [text|
              case val of
                defg:
                  | <_ x y z> -> x
                  | <_ y z> -> z
            |]
            tm' = substitute "val" val tm
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
        in checkTest "CASE" env tm' expectedTy
      ]

    , scope "check switch" $ tests
      [ let tm = BV 0 0
            dataUid = mockCid "dataUid"
            dataTy = unfreeze $ DataTy (UidTy dataUid) []
            expectedTy = dataTy
            env = emptyTypingEnv & varTypes .~ [[Left dataTy]]
        in checkTest "SWITCH" env tm expectedTy
      ]

    , let resolutionState = fromList $
            -- provides Abort, Send, Receive
            (Frank.resolvedDecls ^. globalCids) ++
            [ ("Int", intId)
            , ("Bool", boolId)
            ]
      in scope "check handle" $ tests

        -- both branches should give us a bool
        [ let Right tm = resolveTm resolutionState $
                close closer $
                  forceTm [text|
                    handle abort! : [e , <Abort>]Int with
                      Abort:
                        | <aborting -> k> -> x1
                      | v -> x2
                  |]
              closer = \case
                "abort" -> Just 0
                "x1"    -> Just 1
                "x2"    -> Just 2
                _       -> Nothing
              Just abortId = Frank.resolvedDecls
                ^? globalCids
                 . to HashMap.fromList
                 . ix "Abort"
              abortAbility = Ability OpenAbility [(abortId, [])]
              abortTy = SuspendedTy
                (CompTy []
                  (Peg abortAbility intTy)) -- XXX generalize
              env = emptyTypingEnv
                & typingInterfaces .~ (Frank.resolvedDecls ^. interfaces)
                & varTypes .~ [Left . unfreeze <$> [abortTy, boolTy, boolTy]]
              expectedTy = unfreeze boolTy
          in checkTest "HANDLE (abort)" env tm expectedTy

        , let Right tm = resolveTm resolutionState $
                close closer $
                  forceTm [text|
                    handle val : [e, <Send Bool>, <Receive Bool>]Int with
                      Send Bool:
                        | <send y -> s> -> x1
                      Receive Bool:
                        | <receive -> r> -> x2
                      | v -> x3
                  |]
              closer = \case
                "val" -> Just 0
                "x1"  -> Just 1
                "x2"  -> Just 2
                "x3"  -> Just 3
                _     -> Nothing
              env = emptyTypingEnv
                & typingInterfaces .~ (Frank.resolvedDecls ^. interfaces)
                & varTypes .~ [Left . unfreeze <$> [intTy, boolTy, boolTy, boolTy]]
              expectedTy = unfreeze boolTy
          in checkTest "HANDLE (multi)" env tm expectedTy
        ]

    , let
      in scope "polyvar instantiation" $ tests
        [
        ]

  ]
