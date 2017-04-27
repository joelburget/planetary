{-# language TypeApplications #-}
module Tests.Typecheck where

import Bound (closed)
import Control.Lens
import Test.Tasty
import Test.Tasty.HUnit

-- import Interplanetary.Parser.QQ
import Interplanetary.Syntax
import Interplanetary.Typecheck

checkTest
  :: String
  -> TypingTables Int
  -> TypingEnv Int
  -> TmI
  -> ValTy Int
  -> TestTree
checkTest name tables env tm ty = testCase name $
  runTcM tables env (check tm ty) @?= Right ()

inferTest
  :: String
  -> TypingTables Int
  -> TypingEnv Int
  -> TmI
  -> Either TcErr (ValTy Int)
  -> TestTree
inferTest name tables env tm expected = testCase name $
  runTcM tables env (infer tm) @?= expected

-- TODO: use QQ
exampleInterfaces :: InterfaceTable Int
exampleInterfaces = uIdMapFromList []

dataTypeTable :: DataTypeTable Int
dataTypeTable = mempty

ambientAbility :: Ability Int
ambientAbility = emptyAbility

exampleTables :: TypingTables Int
exampleTables = (dataTypeTable, exampleInterfaces, ambientAbility)

emptyTypingEnv :: TypingEnv Int
emptyTypingEnv = TypingEnv []

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
    [ let domTy = DataTy (mkUid @String "domain") []
          codomTy = DataTy (mkUid @String "codomain") []
          cmdUid = mkUid @String "fire missiles"

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

      in inferTest "COMMAND" tables emptyTypingEnv (CommandTm cmdUid 0) expected
    ]

  , testGroup "TODO: infer app"
    [ let dataUid = mkUid @String "dataUid"
          v1Uid = mkUid @String "v1"
          v2Uid = mkUid @String "v2"
          tm1 = DataTm v1Uid 0 []
          tm2 = DataTm v2Uid 0 []
          ty1 = DataTy v1Uid []
          ty2 = DataTy v2Uid []
          app = Application [tm1, tm2]
          Just f = closed $ lam ["x", "y"] (DataTm dataUid 0 [V"x", V"y"])
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
    -- [ let ty = DataTy (mkUid @String "ty") []
    --   inferTest "COERCE" exampleTables emptyTypingEnv (Annotation
    -- ]
  ]

runTypecheckingTests :: IO ()
runTypecheckingTests = defaultMain unitTests
