{-# language OverloadedLists #-}
module Tests (runTests , runOnlyTests) where

import Data.Text (Text)
import EasyTest

import qualified Planetary.Core.Eval.Test              as Eval
import qualified Planetary.Core.Syntax.Test            as Syntax
import qualified Planetary.Core.Typecheck.Test         as Typecheck
import qualified Planetary.Support.Parser.Test         as Parser
import qualified Planetary.Library.HaskellForeign.Test as HaskellForeign
import qualified Planetary.Library.FrankExamples.Test  as FrankExamples
import qualified Planetary.Library.Meta.Test           as Meta

runTests :: IO ()
runTests = run planetaryTests

runOnlyTests :: Text -> IO ()
runOnlyTests name = runOnly name planetaryTests

planetaryTests :: Test ()
planetaryTests = tests
  [ Syntax.unitTests
  , Eval.unitTests
  , Typecheck.unitTests
  , Parser.unitTests
  , HaskellForeign.unitTests
  , FrankExamples.unitTests
  , Meta.unitTests
  ]

-- unitTests :: TestTree
-- unitTests = scope "ipc unit tests" $ tests
--   [ testCase "expected failure" $ assertBool "" (isJust (topCheck badUnitT))
--   , testCase "check nothingT" $ assertBool "" (isNothing (topCheck nothingT))
--   , testCase "check computation" $ assertBool "" (isNothing (topCheck compT))
--   ]

-- unifyTests :: TestTree
-- unifyTests = scope "ipc unification tests" $ tests
--   [ testCase "1" $ assertBool "" $ isRight $ runTypingContext $ do
--       v1 <- freeVar
--       v2 <- freeVar
--       let tm1 = TypeMultiVal' [v1, TypeLit TypeLiteralText]
--           tm2 = TypeMultiVal' [TypeLit TypeLiteralWord32, v2]
--       tm1 =:= tm2
--   ]
