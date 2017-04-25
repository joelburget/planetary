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
  -> TypingTables Int
  -> TypingEnv Int
  -> TmI
  -> ValTy Int
  -> TestTree
checkTest name tables env tm ty = testCase name $
  runTcM tables env (check tm ty) @=? Right ()

inferTest
  :: String
  -> TypingTables Int
  -> TypingEnv Int
  -> TmI
  -> Either TcErr (ValTy Int)
  -> TestTree
inferTest name tables env tm expected = testCase name $
  runTcM tables env (infer tm) @=? expected

-- TODO: use QQ
exampleInterfaces :: InterfaceTable Int
exampleInterfaces = uIdMapFromList []

exampleTables :: TypingTables Int
exampleTables = (_, exampleInterfaces, _)

emptyTypingEnv :: TypingEnv Int
emptyTypingEnv = TypingEnv []

unitTests :: TestTree
unitTests = testGroup "typechecking"
  [ let env = TypingEnv [Left _]
    in inferTest "VAR 1" exampleTables env (V 0) (Right _)
  , inferTest "VAR 2" exampleTables emptyTypingEnv (V 0) (Left _)
  ]
