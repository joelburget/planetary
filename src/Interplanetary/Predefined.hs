{-# language TypeApplications #-}
module Interplanetary.Predefined where

import Control.Distributed.Process.Serializable (Serializable)
import Control.Lens hiding ((??), op)
import Control.Monad.Except
import Control.Monad.State
import Data.Dynamic

import Interplanetary.Eval
import Interplanetary.Syntax
import Interplanetary.Typecheck
import Interplanetary.Util

-- TODO: this is really a "haskell int"
intTy :: ValTyI
intTy = DataTy intId []

boolTy :: ValTyI
boolTy = DataTy boolId []

strTy :: ValTyI
strTy = DataTy strId []

-- TODO: some way to declare both implementation and type at the same time
interfaceTable :: InterfaceTable Int
interfaceTable = uIdMapFromList
  [ (intOpsId, EffectInterface []
    [ CommandDeclaration [intTy, intTy] intTy -- +
    , CommandDeclaration [intTy, intTy] intTy -- -
    ])
  , (boolOpsId, EffectInterface []
    [ CommandDeclaration [boolTy, boolTy] boolTy -- &&
    , CommandDeclaration [boolTy, boolTy] boolTy -- ||
    ])
  , (strOpsId, EffectInterface []
    [ CommandDeclaration [strTy, strTy] strTy -- concat
    ])
  ]

foreignContinuations :: ForeignContinuations Int Int
foreignContinuations = uIdMapFromList
  [ (intOpsId, [ liftBinaryOp @Int (+) , liftBinaryOp @Int (-) ])
  , (boolOpsId, [ liftBinaryOp (&&) , liftBinaryOp (||) ])
  , (strOpsId, [ liftBinaryOp @String (++) ])
  ]

lookupForeign :: Serializable a => UId -> ForeignM Int Int a
lookupForeign uid = do
  dyn <- gets (^? ix uid) >>= (?? IndexErr)
  case fromDynamic dyn of
    Nothing -> throwError FailedDynamicConversion
    Just i -> pure i

writeForeign :: Serializable a => a -> ForeignM Int Int UId
writeForeign a = do
  let uid = mkUid a
  modify (& ix uid .~ toDyn a)
  pure uid

liftBinaryOp
  :: Serializable s
  => (s -> s -> s) -> (Spine a b -> ForeignM a b (Tm a b))
liftBinaryOp op [ForeignDataTm uid1, ForeignDataTm uid2] = do
  i <- op <$> lookupForeign uid1 <*> lookupForeign uid2
  ForeignDataTm <$> writeForeign i
liftBinaryOp _ _ = throwError FailedForeignFun

-- TODO: use QQ
exampleDataTypes :: DataTypeTable String
exampleDataTypes = uIdMapFromList
  -- void has no constructor
  [ (voidUid, [])
  -- unit has a single nullary constructor
  , (unitUid, [[]])
  -- bool has two nullary constructors
  , (boolUid, [[], []])
  -- `data Id a = Id a`
  , (idUid, [[VTy"a"]])
  -- A, B = D [R] | { C } | X
  , (valueTyUid, [
      -- [uidUid
    ])
  ]
