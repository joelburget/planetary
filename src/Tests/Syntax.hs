{-# language Rank2Types #-}
module Tests.Syntax where

import Test.Tasty
import Test.Tasty.HUnit

import Interplanetary.Syntax

unitTy :: forall a. ValTy UId a
unitTy = DataTy unitId []

unitTests :: TestTree
unitTests = testGroup "syntax"
  [ testCase "extendAbility 1" $
    let uidMap = uIdMapFromList [(unitId, [TyArgVal unitTy])]
        actual :: Ability UId String
        actual = extendAbility emptyAbility (Adjustment uidMap)
        expected = Ability OpenAbility uidMap
    in expected @?= actual
  , testCase "extendAbility 2" $
    let uidMap = uIdMapFromList [(unitId, [TyArgVal unitTy])]
        actual :: Ability UId String
        actual = extendAbility closedAbility (Adjustment uidMap)
        expected = Ability ClosedAbility uidMap
    in expected @?= actual
  , testGroup "TODO: unify" []
  ]
