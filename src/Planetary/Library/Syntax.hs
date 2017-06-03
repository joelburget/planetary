{-# language QuasiQuotes #-}
{-# language ScopedTypeVariables #-}
module Planetary.Library.Syntax where

import Network.IPLD

import Planetary.Core
import Planetary.Support.Ids
import Planetary.Support.Parser.QQ
import Planetary.Util

vector, uidMap, lfix :: Vector TyArgI -> ValTyI

vector = DataTy vectorId
uidMap = DataTy uidMapId
lfix   = DataTy lfixId

dataTypeTable :: DataTypeTable Cid Int
interfaceTable :: InterfaceTable Cid Int
( dataTypeTable :: DataTypeTable Cid Int,
  interfaceTable :: InterfaceTable Cid Int,
  _,
  _) = [declarations|

data InitiateAbility
  = <openAbility>
  | <closedAbility>

-- mutually recursive family of data types
data TyFamily
  = <valTy>
  | <compTy>
  | <peg>
  | <tyArg>
  | <ability>

data Ty uid a ty
  -- ValTy
  = <dataTy uid ($vector ty)>
  | <suspendedTy ty>
  | <variableTy a>

  -- CompTy
  | <compTy ($vector ty) ty>

  -- Peg
  | <peg ty ty>

  -- TyArg
  | <tyArgVal ty>
  | <tyArgAbility ty>

  -- Ability
  | <ability InitiateAbility ($uidMap uid ty)>

data Adjustment uid a
  = <adjustment ($uidMap uid ($lfix (Ty uid a)))>
|]
