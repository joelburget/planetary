{-# language QuasiQuotes #-}
module Tests.Typecheck where

import qualified Data.IntMap as IntMap
import Test.Tasty
import Test.Tasty.HUnit
import Text.Trifecta

-- import Interplanetary.Parser.QQ
import Interplanetary.Syntax
import Interplanetary.Typecheck

checkTest
  :: String
  -> Ability Int
  -> TypingTables Int
  -> TypingEnv Int
  -> TmI
  -> ValTy Int
  -> TestTree
checkTest name ability tables env tm ty = testCase name $
  runTcM (ability, tables) env (check tm ty) @=? Right ()

inferTest
  :: String
  -> Ability Int
  -> TypingTables Int
  -> TypingEnv Int
  -> TmI
  -> Either TcErr (ValTy Int)
  -> TestTree
inferTest name ability tables env tm expected = testCase name $
  runTcM (ability, tables) env (infer tm) @=? expected

-- TODO: use QQ
exampleInterfaces :: InterfaceTable String
exampleInterfaces = uIdMapFromList []

exampleTables :: TypingTables String
exampleTables = exampleInterfaces

emptyTypingEnv :: TypingEnv String
emptyTypingEnv = TypingEnv []

unitTests :: TestTree
unitTests = testGroup "typechecking"
  [ let env = TypingEnv [Left _]
    in inferTest "VAR 1" exampleTables env (V"x") (Right _)
  , inferTest "VAR 2" exampleTables emptyTypingEnv (V"x") (Left _)
  ]
