{-# language QuasiQuotes #-}
module Tests.Eval where

import qualified Data.IntMap as IntMap
import Test.Tasty
import Test.Tasty.HUnit
import Text.Trifecta

import Interplanetary.Parser.QQ

checkTest
  :: String
  -> TypingTables String
  -> TypingEnv String
  -> TmI
  -> ValTy Int
  -> TestTree
checkTest name tables env tm ty = testCase name $
  runTcM tables env (check tm ty) @=? Right ()

inferTest
  :: String
  -> TypingTables String
  -> TypingEnv String
  -> TmI
  -> Either TcErr (ValTy Int)
  -> TestTree
inferTest name tables env tm expected = testCase name $
  runTcM tables env (infer tm) @=? expected

-- TODO: use QQ
exampleDataTypes :: DataTypeTable String
exampleDataTypes = uidMapFromList
  -- void has no constructor
  [ (1, [])
  -- unit has a single nullary constructor
  , (2, [[]])
  -- `data Id a = Id a`
  , (3, [[VTy"a"]])
  ]

-- TODO: use QQ
exampleInterfaces :: InterfaceTable String
exampleInterfaces = uidMapFromList []

exampleTables :: TypingTables String
exampleTables = (exampleDataTypes, exampleInterfaces)

emptyTypingEnv :: TypingEnv String
emptyTypingEnv = TypingEnv []

unitTests :: TestTree
unitTests = testGroup "typechecking"
  [ let env = TypingEnv [Left _]
    in inferTest "VAR 1" exampleTables env (V"x") (Right _)
  , inferTest "VAR 2" exampleTables emptyTypingEnv (V"x") (Left _)
  ]
