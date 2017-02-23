{-# language OverloadedLists #-}
module Interplanetary.Examples where

import Interplanetary.Genesis

unit :: HeapVal
unit = HeapMultiVal []

nothing :: HeapVal
nothing = HeapTagged 0 unit

-- should check
nothingT :: Toplevel
nothingT = Return [HeapVal nothing] ::: TypeTagged 0 (TypeMultiVal [])

badUnitT :: Toplevel
badUnitT = Return [HeapVal unit] ::: TypeTagged 0 (TypeMultiVal [])

elimNothing :: Case
elimNothing = Case [Return [HeapVal unit]]

comp :: Term
comp = CutCase elimNothing (HeapVal (HeapTagged 0 nothing))

compT :: Toplevel
compT = comp ::: TypeMultiVal []

