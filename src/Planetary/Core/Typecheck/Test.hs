{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
module Planetary.Core.Typecheck.Test where

import Bound (closed)
import Control.Lens
import Control.Unification (freeze, unfreeze)
import Control.Unification.IntVar
import Data.ByteString (ByteString)
import NeatInterpolation
import Network.IPLD
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
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
      in inferTest "VAR 1" env (V 0) (Right ty)
    , inferTest "VAR 2" emptyTypingEnv (V 0) (Left (LookupVarTy 0))
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

          cmd = CommandV cmdUid 0

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
        Just f = closed $ Lam ["x", "y"] $
          DataTm dataUid 0 [V"x", V"y"]
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

  , testGroup "infer annotation" []
    -- [ let ty = DataTy (mockCid "ty") []
    --   inferTest "COERCE" emptyTypingEnv (Annotation
    -- ]

  , testGroup "TODO: check lambda" []

    -- , testGroup "check case"
    --   [ let abcdUid = mockCid "abcd"
    --         abcdTy = DataTy abcdUid []
    --         abcdVal = DataTm abcdUid 0 []
    --         otherUid = mockCid "123424321432"
    --         val = DataTm otherUid 1 [abcdVal, abcdVal]
    --         tm = -- closed $ substitute "val" val $
    --           [tmExp|
    --             case val of
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
            dataTy = unfreeze $ DataTy dataUid []
            expectedTy = dataTy
            env = emptyTypingEnv & varTypes .~ [Left dataTy]
        in checkTest "SWITCH" env tm expectedTy
      ]

    , let
          -- simpleTables = _
      in testGroup "check handle"
        [ let _tm = forceTm [text|
                handle abort! : [e , <Abort>]HaskellInt with
                  Abort:
                    | <aborting -> k> -> 1
                  | v -> 2
              |]
          in testCase "HANDLE (abort)" (pure ())
             -- checkTest "HANDLE (abort)" emptyTypingEnv env tm' expectedTy

        , let _tm = forceTm [text|
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
