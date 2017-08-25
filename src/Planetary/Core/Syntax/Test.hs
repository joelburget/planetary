{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language TypeFamilies #-}
module Planetary.Core.Syntax.Test (unitTests) where

import Network.IPLD
import EasyTest

import Planetary.Core
import Planetary.Support.Ids

unitTy :: ValTy Cid
unitTy = DataTy (UidTy unitId) []

unitTests :: Test ()
unitTests = scope "syntax" $ tests
  [ scope "extendAbility 1" $
    let uidMap = [(unitId, [TyArgVal unitTy])]
        actual :: Ability Cid
        actual = extendAbility emptyAbility (Adjustment uidMap)
        expected = Ability OpenAbility uidMap
    in expect $ expected == actual
  , scope "extendAbility 2" $
    let uidMap = [(unitId, [TyArgVal unitTy])]
        actual :: Ability Cid
        actual = extendAbility closedAbility (Adjustment uidMap)
        expected = Ability ClosedAbility uidMap
    in expect $ expected == actual
  , scope "TODO: unify" $ tests []
  ]
