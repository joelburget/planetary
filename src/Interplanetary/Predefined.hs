{-# language OverloadedLists #-}
module Interplanetary.Predefined where

import qualified Data.IntMap as IntMap

import Interplanetary.Syntax

-- types

valueTyUid, computationTyUid, pegUid, tyVarUid, tyArgUid, polyTyUid :: Uid
abilityUid, adjustmentUid, tyEnvUid :: Uid
valueTyUid = 0
computationTyUid = 1
pegUid = 2
tyVarUid = 3
tyArgUid = 4
polyTyUid = 5
abilityUid = 6
adjustmentUid = 7
tyEnvUid = 8

-- terms

useUid, constructionUid, spineUid :: Uid
useUid = 9
constructionUid = 10
spineUid = 11

dataTypeTable :: DataTypeTable
dataTypeTable = IntMap.fromList
  [ ]
