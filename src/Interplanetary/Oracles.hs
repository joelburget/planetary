{-# language GADTs #-}
module Interplanetary.Oracles where

import Interplanetary.Genesis
import Interplanetary.Meta

-- Idea: For a state-carrying computation, allocate a `var` token as a handle.

todo' :: forall a. a
todo' = todo "oracles"

data CovalueOracleDef
  = CovalueOracleDef GenesisTy GenesisCovalue

data ValueOracleDef
  = ValueOracleDef GenesisTy GenesisValue

quoteOracle :: CovalueOracleDef
quoteOracle = CovalueOracleDef
  todo'
  todo' -- quote

spliceOracle :: CovalueOracleDef
spliceOracle = CovalueOracleDef
  todo'
  todo' -- splice

randomIntOracle :: CovalueOracleDef
randomIntOracle = CovalueOracleDef
  todo'
  -- XXX the implementation here maintains state
  todo'

intAdditionOracle :: CovalueOracleDef
intAdditionOracle = CovalueOracleDef
  todo'
  -- XXX the implementation has the wrong type
  todo'

uidOracle :: CovalueOracleDef
uidOracle = CovalueOracleDef
  todo'
  -- XXX the implementation here maintains state
  todo'
