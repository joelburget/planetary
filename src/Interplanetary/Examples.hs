{-# language OverloadedLists #-}
module Interplanetary.Examples where

import Interplanetary.Genesis

unit :: HeapVal
unit = HeapMultiVal []

nothing :: HeapVal
nothing = HeapTagged 0 unit

-- should check
nothingT :: Toplevel
nothingT =
  let ty = TypeMultiVal' [TypeTagged' 0 (TypeMultiVal' [])]
      tm = Return [HeapVal nothing]
  in tm ::: ty

returnUnit :: Toplevel
returnUnit =
  let ty = TypeMultiVal' [TypeTagged' 0 (TypeMultiVal' [])]
      tm = Return [HeapVal (HeapTagged 0 (HeapAtom (Term (Return []))))]
  in tm ::: ty

returnNothing :: Toplevel
returnNothing = Return [] ::: TypeMultiVal' []

elimNothing :: Case
elimNothing = Case [Return [HeapVal unit]]

comp :: Term
comp = CutCase elimNothing (HeapVal (HeapTagged 0 nothing))

compT :: Toplevel
compT = comp ::: TypeMultiVal' []

