{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
module Planetary.Core.Typecheck.Test where

import Bound (closed)
import Control.Lens
import Data.ByteString (ByteString)
import Network.IPLD
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Support.Parser.QQ

checkTest
  :: String
  -> TypingEnvI
  -> TypingStateI
  -> TmI
  -> ValTyI
  -> TestTree
checkTest name tables env tm ty = testCase name $
  runTcM tables env (check tm ty) @?= Right ()

inferTest
  :: String
  -> TypingEnvI
  -> TypingStateI
  -> TmI
  -> Either TcErr ValTyI
  -> TestTree
inferTest name tables env tm expected = testCase name $
  runTcM tables env (infer tm) @?= expected

-- TODO: use QQ
exampleInterfaces :: InterfaceTableI
exampleInterfaces = uIdMapFromList []

dataTypeTable :: DataTypeTableI
dataTypeTable = mempty

ambientAbility :: AbilityI
ambientAbility = emptyAbility

emptyTypingEnv :: TypingEnvI
emptyTypingEnv = TypingEnv dataTypeTable exampleInterfaces ambientAbility

emptyTypingState :: TypingStateI
emptyTypingState = TypingState []

mockCid :: ByteString -> Cid
mockCid = mkCid

unitTests :: TestTree
unitTests = testGroup "typechecking"
  [ testGroup "infer variable"
    [ let ty = VariableTy 787
          env = TypingState [Left ty]
      in inferTest "VAR 1" emptyTypingEnv env (V 0) (Right ty)
    , inferTest "VAR 2" emptyTypingEnv emptyTypingState (V 0) (Left (LookupVarTy 0))
    ]

  , testGroup "TODO: infer polyvar"
    [
    ]

  , testGroup "infer command"
    [ let domTy = DataTy (mockCid "domain") []
          codomTy = DataTy (mockCid "codomain") []
          cmdUid = mockCid "fire missiles"

          -- TODO: this duplication between ambient and interfaces is so bad
          interfaces = uIdMapFromList
            [ (cmdUid, EffectInterface []
                [CommandDeclaration [domTy] codomTy]
              )
            ]

          ambient = extendAbility emptyAbility $ Adjustment $ uIdMapFromList
            [ (cmdUid, [TyArgVal domTy])
            -- TODO: what does it mean to have an ability here?
            -- [ (cmdUid, [TyArgVal domTy, TyArgAbility _])
            ]

          tables = emptyTypingEnv & typingInterfaces .~ interfaces
                                  & typingAbilities .~ ambient

          cmd = CommandV cmdUid 0

          expected = Right $
            SuspendedTy $ CompTy [domTy] $ Peg ambient codomTy

      in inferTest "COMMAND" tables emptyTypingState cmd expected
    ]

  , let dataUid = mockCid "dataUid"
        v1Id = mockCid "v1"
        v2Id = mockCid "v2"
        tm1 = DataTm v1Id 0 []
        tm2 = DataTm v2Id 0 []
        ty1 = DataTy v1Id []
        ty2 = DataTy v2Id []
        constr1 = ConstructorDecl "constr1" [ty1, ty2]
        constr2 = ConstructorDecl "constr2" []

        app = Application [tm1, tm2]
        Just f = closed $ Lam ["x", "y"] $
          DataTm dataUid 0 [V"x", V"y"]
        resultTy = DataTy dataUid [TyArgVal ty1, TyArgVal ty2]

        goodAnnF = Annotation f $ SuspendedTy $
          CompTy [ty1, ty2] (Peg emptyAbility resultTy)
        expected = Right resultTy

        baddAnnF = Annotation f $ SuspendedTy $
          CompTy [ty1, ty1] (Peg emptyAbility resultTy)
        expectedBad = Left (TyUnification ty1 ty2)

        tables = emptyTypingEnv & typingData .~ uIdMapFromList
          [ (dataUid, DataTypeInterface [] [constr1])
          , (v1Id, DataTypeInterface [] [constr2])
          , (v2Id, DataTypeInterface [] [constr2])
          ]

    in testGroup "infer app"
      [ inferTest "APP (1)" tables emptyTypingState (Cut app goodAnnF) expected
      , inferTest "APP (2)" tables emptyTypingState (Cut app baddAnnF) expectedBad
      ]

  , testGroup "infer annotation" []
    -- [ let ty = DataTy (mockCid "ty") []
    --   inferTest "COERCE" emptyTypingEnv emptyTypingState (Annotation
    -- ]

  , testGroup "TODO: check lambda" []

  , testGroup "check data"
    [ let v1Id = mockCid "v1"
          tm1 = DataTm v1Id 0 []
          ty1 = DataTy v1Id []
          tables = emptyTypingEnv & typingData .~ uIdMapFromList
            [ (v1Id, DataTypeInterface [] [ConstructorDecl "constr" []]) ]
      in checkTest "DATA (simple)" tables emptyTypingState tm1 ty1
    , let dataUid = mockCid "dataUid"
          v1Id = mockCid "v1"
          v2Id = mockCid "v2"
          tm1 = DataTm v1Id 0 []
          tm2 = DataTm v2Id 0 []
          ty1 = DataTy v1Id []
          ty2 = DataTy v2Id []
          constr1 = ConstructorDecl "constr1" [ty1, ty2]
          constr2 = ConstructorDecl "constr2" []
          tables = emptyTypingEnv & typingData .~ uIdMapFromList
            [ (dataUid, DataTypeInterface [] [constr1])
            , (v1Id, DataTypeInterface [] [constr2])
            , (v2Id, DataTypeInterface [] [constr2])
            ]
          tm = DataTm dataUid 0 [tm1, tm2]
          expectedTy = DataTy dataUid [TyArgVal ty1, TyArgVal ty2]
      in checkTest "DATA (args)" tables emptyTypingState tm expectedTy
    ]

    -- , testGroup "check case"
    --   [ let abcdUid = mockCid "abcd"
    --         abcdTy = DataTy abcdUid []
    --         abcdVal = DataTm abcdUid 0 []
    --         otherUid = mockCid "123424321432"
    --         val = DataTm otherUid 1 [abcdVal, abcdVal]
    --         tm = -- closed $ substitute "val" val $
    --           [tmExp|
    --             case $val of
    --               123424321432:
    --                 | x y z -> x
    --                 | y z -> z
    --           |]
    --         -- Just (dataTys, _) = [declarations|
    --         --     data =
    --         --       |
    --         --     data =
    --         --       |
    --         --   |]
    --         tables = emptyTypingEnv & typingData .~ uIdMapFromList
    --           [ (abcdUid, [[]])
    --           , (otherUid,
    --             [ [abcdTy, abcdTy, abcdTy]
    --             , [abcdTy, abcdTy]
    --             ])
    --           ]
    --         expectedTy = abcdTy
    --         env = TypingState
    --           [
    --           ]
    --     in checkTest "CASE" tables env tm expectedTy
    --   ]

    , testGroup "check switch"
      [ let tm = V 0
            dataUid = mockCid "dataUid"
            dataTy = DataTy dataUid []
            expectedTy = dataTy
            env = TypingState [Left dataTy]
        in checkTest "SWITCH" emptyTypingEnv env tm expectedTy
      ]

    , let
          -- simpleTables = _
      in testGroup "check handle"
        [ let _tm = [tmExp|
                handle abort! : [e , <Abort>]HaskellInt with
                  Abort:
                    | <aborting -> k> -> 1
                  | v -> 2
              |]
          in testCase "HANDLE (abort)" (pure ())
             -- checkTest "HANDLE (abort)" emptyTypingEnv env tm' expectedTy

        , let _tm = [tmExp|
                handle x : peg with
                  Send X:
                    -- TODO: Should we switch to the original syntax?
                    -- <send y -> s>
                    | <send y -> s> -> 1
                  Receive Y:
                    | <receive -> r> -> 2
                  | v -> 3
              |]
          in testCase "HANDLE (multi)" (pure ())
             -- checkTest "HANDLE (multi)" simpleTables env tm expectedTy
        ]

  ]

runTypecheckingTests :: IO ()
runTypecheckingTests = defaultMain unitTests
