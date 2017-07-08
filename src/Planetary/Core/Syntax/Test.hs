{-# language OverloadedLists #-}
{-# language TypeFamilies #-}
module Planetary.Core.Syntax.Test (unitTests) where

import Network.IPLD
import Test.Tasty
import Test.Tasty.HUnit

import Planetary.Core
import Planetary.Support.Ids

unitTy :: ValTy Cid
unitTy = DataTy (UidTy unitId) []

unitTests :: TestTree
unitTests = testGroup "syntax"
  [ testCase "extendAbility 1" $
    let uidMap = [(unitId, [TyArgVal unitTy])]
        actual :: Ability Cid
        actual = extendAbility emptyAbility (Adjustment uidMap)
        expected = Ability OpenAbility uidMap
    in expected @?= actual
  , testCase "extendAbility 2" $
    let uidMap = [(unitId, [TyArgVal unitTy])]
        actual :: Ability Cid
        actual = extendAbility closedAbility (Adjustment uidMap)
        expected = Ability ClosedAbility uidMap
    in expected @?= actual
  , testGroup "TODO: unify" []
  ]
