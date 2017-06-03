{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Tests.Typecheck where

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
  -> TypingTables Cid Int
  -> TypingEnv Cid Int
  -> TmI
  -> ValTy Cid Int
  -> TestTree
checkTest name tables env tm ty = testCase name $
  runTcM tables env (check tm ty) @?= Right ()

inferTest
  :: String
  -> TypingTables Cid Int
  -> TypingEnv Cid Int
  -> TmI
  -> Either TcErr (ValTy Cid Int)
  -> TestTree
inferTest name tables env tm expected = testCase name $
  runTcM tables env (infer tm) @?= expected

-- TODO: use QQ
exampleInterfaces :: InterfaceTable Cid Int
exampleInterfaces = uIdMapFromList []

dataTypeTable :: DataTypeTable Cid Int
dataTypeTable = mempty

ambientAbility :: Ability Cid Int
ambientAbility = emptyAbility

exampleTables :: TypingTables Cid Int
exampleTables = (dataTypeTable, exampleInterfaces, ambientAbility)

emptyTypingEnv :: TypingEnv Cid Int
emptyTypingEnv = TypingEnv []

mockCid :: ByteString -> Cid
mockCid = mkCid

unitTests :: TestTree
unitTests = testGroup "typechecking"
  [ testGroup "infer variable"
    [ let ty = VariableTy 787
          env = TypingEnv [Left ty]
      in inferTest "VAR 1" exampleTables env (V 0) (Right ty)
    , inferTest "VAR 2" exampleTables emptyTypingEnv (V 0) (Left LookupVarTy)
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

          tables = exampleTables & _2 .~ interfaces
                                 & _3 .~ ambient

          expected = Right $
            SuspendedTy $ CompTy [domTy] $ Peg ambient codomTy

      in inferTest "COMMAND" tables emptyTypingEnv (CommandV cmdUid 0 []) expected
    ]

  , testGroup "infer app"
    [ let dataUid = mockCid "dataUid"
          v1Uid = mockCid "v1"
          v2Uid = mockCid "v2"
          tm1 = DataTm v1Uid 0 []
          tm2 = DataTm v2Uid 0 []
          ty1 = DataTy v1Uid []
          ty2 = DataTy v2Uid []
          app = Application [tm1, tm2]
          Just f = closed $ Lam ["x", "y"] $
            DataTm dataUid 0 [V"x", V"y"]
          resultTy = DataTy dataUid [TyArgVal ty1, TyArgVal ty2]
          annF = Annotation f $ SuspendedTy $
            CompTy [ty1, ty2] (Peg emptyAbility resultTy)
          expected = Right resultTy
          tables = exampleTables & _1 .~ uIdMapFromList
            [ (dataUid, [[ty1, ty2]])
            , (v1Uid, [[]])
            , (v2Uid, [[]])
            ]
      in inferTest "APP" tables emptyTypingEnv (Cut app annF) expected
    ]

  , testGroup "infer annotation" []
    -- [ let ty = DataTy (mockCid "ty") []
    --   inferTest "COERCE" exampleTables emptyTypingEnv (Annotation
    -- ]

  , testGroup "TODO: check lambda" []

  , testGroup "check data"
    [ let v1Uid = mockCid "v1"
          tm1 = DataTm v1Uid 0 []
          ty1 = DataTy v1Uid []
          tables = exampleTables & _1 .~ uIdMapFromList
            [ (v1Uid, [[]]) ]
      in checkTest "DATA (simple)" tables emptyTypingEnv tm1 ty1
    , let dataUid = mockCid "dataUid"
          v1Uid = mockCid "v1"
          v2Uid = mockCid "v2"
          tm1 = DataTm v1Uid 0 []
          tm2 = DataTm v2Uid 0 []
          ty1 = DataTy v1Uid []
          ty2 = DataTy v2Uid []
          tables = exampleTables & _1 .~ uIdMapFromList
            [ (dataUid, [[ty1, ty2]])
            , (v1Uid, [[]])
            , (v2Uid, [[]])
            ]
          tm = DataTm dataUid 0 [tm1, tm2]
          expectedTy = DataTy dataUid [TyArgVal ty1, TyArgVal ty2]
      in checkTest "DATA (args)" tables emptyTypingEnv tm expectedTy
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
    --         tables = exampleTables & _1 .~ uIdMapFromList
    --           [ (abcdUid, [[]])
    --           , (otherUid,
    --             [ [abcdTy, abcdTy, abcdTy]
    --             , [abcdTy, abcdTy]
    --             ])
    --           ]
    --         expectedTy = abcdTy
    --         env = TypingEnv
    --           [
    --           ]
    --     in checkTest "CASE" tables env tm expectedTy
    --   ]

    , testGroup "check switch"
      [ let tm = V 0
            dataUid = mockCid "dataUid"
            dataTy = DataTy dataUid []
            expectedTy = dataTy
            env = TypingEnv [Left dataTy]
        in checkTest "SWITCH" exampleTables env tm expectedTy
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
             -- checkTest "HANDLE (abort)" exampleTables env tm' expectedTy

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
