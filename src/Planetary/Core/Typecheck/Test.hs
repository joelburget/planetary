{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
module Planetary.Core.Typecheck.Test
  ( unitTests
  , runTypecheckingTests
  , checkTest
  , emptyTypingEnv
  ) where

import Control.Lens
import Control.Unification (freeze, unfreeze)
import Control.Unification.IntVar
import Data.ByteString (ByteString)
import NeatInterpolation
import Network.IPLD
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Support.NameResolution
import Planetary.Support.Parser

checkTest
  :: String
  -> TypingEnvI
  -> TmI
  -> UTy IntVar
  -> TestTree
checkTest name tables tm ty = testCase name $
  runTcM tables (check tm ty) @?= Right ()

inferTest
  :: String
  -> TypingEnvI
  -> TmI
  -> Either TcErr (UTy IntVar)
  -> TestTree
inferTest name tables tm expected = testCase name $
  (freeze <$> runTcM tables (infer tm)) @?= (freeze <$> expected)

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

unitTests :: TestTree
unitTests = testGroup "typechecking"
  [ testGroup "infer variable"
    [ let ty = FreeVariableTyU "hippo"
          env = emptyTypingEnv & varTypes .~ [Left ty]
      in inferTest "VAR 1" env (BV 0) (Right ty)
    , inferTest "VAR 2" emptyTypingEnv (BV 0) (Left (LookupVarTy 0))
    ]

  , testGroup "TODO: infer polyvar"
    [
    ]

  , testGroup "infer command"
    [ let domTy = DataTy (mockCid "domain") []
          codomTy = DataTy (mockCid "codomain") []
          cmdUid = mockCid "fire missiles"

          -- TODO: this duplication between ambient and interfaces is so bad
          cmdIfaces = uIdMapFromList
            [ (cmdUid, EffectInterface []
                [CommandDeclaration "fire missiles" [domTy] codomTy]
              )
            ]

          ambient = extendAbility emptyAbility $ Adjustment $ uIdMapFromList
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
        tm1 = DataTm v1Id 0 []
        tm2 = DataTm v2Id 0 []
        ty1 = DataTy v1Id []
        ty2 = DataTy v2Id []
        ty1ty2vals = [TyArgVal ty1, TyArgVal ty2]
        constr1 = ConstructorDecl "constr1" [ty1, ty2]
        constr2 = ConstructorDecl "constr2" []

        app = Application [tm1, tm2]
        f = Lam ["x", "y"] $ DataTm dataUid 0 [FV"x", FV"y"]
        resultTy = DataTy dataUid ty1ty2vals

        goodAnnF = Annotation f $ SuspendedTy $
          CompTy [ty1, ty2] (Peg emptyAbility resultTy)
        expected = Right (unfreeze resultTy)

        baddAnnF = Annotation f $ SuspendedTy $
          CompTy [ty1, ty1] (Peg emptyAbility resultTy)
        expectedBad = Left (MismatchFailure undefined undefined)

        tables = emptyTypingEnv & typingData .~ uIdMapFromList
          [ (dataUid, DataTypeInterface [] [constr1 ty1ty2vals])
          , (v1Id, DataTypeInterface [] [constr2 []])
          , (v2Id, DataTypeInterface [] [constr2 []])
          ]

    in testGroup "(sharing data defns)"
         [ testGroup "infer app"
           [ inferTest "APP (1)" tables (Cut app goodAnnF) expected
           , inferTest "APP (2)" tables (Cut app baddAnnF) expectedBad
           ]
         , testGroup "check data"
           [ let tables' = emptyTypingEnv & typingData .~ uIdMapFromList
                   [ (v1Id, DataTypeInterface [] [ConstructorDecl "constr" [] []]) ]
             in checkTest "DATA (simple)" tables' tm1 (unfreeze ty1)
           , let tm = DataTm dataUid 0 [tm1, tm2]
                 expectedTy = DataTy dataUid ty1ty2vals
             in checkTest "DATA (args)" tables tm (unfreeze expectedTy)
           ]
         ]

  , testGroup "infer annotation"
    [ let cid = mockCid "ty"
          ty = DataTy cid []
          tm = Annotation (DataConstructor cid 0 []) ty
      in inferTest "COERCE" emptyTypingEnv tm (Right (unfreeze ty))
    ]

  , testGroup "TODO: check lambda" []

    , testGroup "check case"
      [ let abcdUid = mockCid "abcd"
            defgUid = mockCid "123424321432"
            abcdTy = DataTy abcdUid []
            abcdVal = DataTm abcdUid 0 []
            val = DataTm defgUid 1 [abcdVal, abcdVal]
            resolutionState = mempty
              & ix "abcd" .~ abcdUid
              & ix "defg" .~ defgUid
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
            env = emptyTypingEnv & typingData .~ uIdMapFromList
              [ (abcdUid, DataTypeInterface []
                [ ConstructorDecl "abcd" [] []
                ])
              , (defgUid, DataTypeInterface []
                [ ConstructorDecl "defg1" [abcdTy, abcdTy, abcdTy] []
                , ConstructorDecl "defg2" [abcdTy, abcdTy]         []
                ])
              ]
            expectedTy = unfreeze abcdTy
        in checkTest "CASE" env tm expectedTy
      ]

    , testGroup "check switch"
      [ let tm = BV 0
            dataUid = mockCid "dataUid"
            dataTy = unfreeze $ DataTy dataUid []
            expectedTy = dataTy
            env = emptyTypingEnv & varTypes .~ [Left dataTy]
        in checkTest "SWITCH" env tm expectedTy
      ]

          -- TODO: extend with Abort, Send, Receive
    , let env = emptyTypingEnv
          resolutionState = mempty
      in testGroup "check handle"
        [ let Right tm = resolveTm resolutionState $ forceTm [text|
                handle abort! : [e , <Abort>]HaskellInt with
                  Abort:
                    | <aborting -> k> -> 1
                  | v -> 2
              |]
              expectedTy = unfreeze $ DataTy (mockCid "XXX") []
          in checkTest "HANDLE (abort)" env tm expectedTy

        , let Right tm = resolveTm resolutionState $ forceTm [text|
                handle x : peg with
                  Send X:
                    | <send y -> s> -> 1
                  Receive Y:
                    | <receive -> r> -> 2
                  | v -> 3
              |]
              expectedTy = unfreeze $ DataTy (mockCid "XXX") []
          in checkTest "HANDLE (multi)" env tm expectedTy
        ]

    , let
      in testGroup "polyvar instantiation"
        [
        ]

  ]

runTypecheckingTests :: IO ()
runTypecheckingTests = defaultMain unitTests
