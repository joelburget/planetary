module Tests.Checking where

-- import Data.Either
-- import qualified Data.IntMap as IntMap
-- import Test.Tasty
-- import Test.Tasty.HUnit

-- import Interplanetary.Syntax

-- idTm :: Construction''
-- idTm = Lambda 1 (ConstructUse (Variable 0))

-- assertChecks :: Construction'' -> ValTy -> Assertion
-- assertChecks tm ty
--   = assertBool "assertChecks" (isRight (runCheckMBasic (check tm ty)))

-- assertDoesn'tCheck :: Construction'' -> ValTy -> Assertion
-- assertDoesn'tCheck tm ty
--   = assertBool "assertDoesn'tCheck" (isLeft (runCheckMBasic (check tm ty)))

-- unitTests :: TestTree
-- unitTests = testGroup "checking"
--   [ testCase "(\\x -> x : Unit -> [e]Unit)" $
--     let ty = SuspendedTy (CompTy [unitTy] (Peg emptyAbility unitTy))
--     in assertChecks idTm ty

--   , testCase "(\\x -> x : Unit -> [0]Unit)" $
--     let ty = SuspendedTy (CompTy [unitTy] (Peg closedAbility unitTy))
--     in assertChecks idTm ty

--   , testCase "unit : Unit" $ assertChecks unitVal unitTy
--   , testCase "unit /: Zero" $ assertDoesn'tCheck unitVal zeroTy

--   -- , testCase "handle" $
--   ]
