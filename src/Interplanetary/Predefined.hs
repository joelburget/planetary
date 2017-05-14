{-# language TypeApplications #-}
module Interplanetary.Predefined where

import Control.Lens hiding ((??), op)
import Control.Monad.Except
import Control.Monad.State
import Network.IPLD as IPLD

import Interplanetary.Eval
import Interplanetary.Syntax
import Interplanetary.Typecheck
import Interplanetary.UIds
import Interplanetary.Util

-- TODO: this is really a "haskell int"
intTy :: ValTyI
intTy = DataTy intId []

boolTy :: ValTyI
boolTy = DataTy boolId []

strTy :: ValTyI
strTy = DataTy strId []

uidTy :: ValTyI
uidTy = DataTy uidId []

-- TODO: some way to declare both implementation and type at the same time
interfaceTable :: InterfaceTable Cid Int
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
  , (uidOpsId, EffectInterface []
    [ CommandDeclaration [] uidTy -- generateUid
    ])
  ]

foreignContinuations :: ForeignContinuations Int Int
foreignContinuations = uIdMapFromList
  [ (intOpsId, [ liftBinaryOp @Int (+) , liftBinaryOp @Int (-) ])
  , (boolOpsId, [ liftBinaryOp (&&) , liftBinaryOp (||) ])
  , (strOpsId, [ liftBinaryOp @String (++) ])
  ]

lookupForeign :: IsIpld a => Cid -> ForeignM Int Int a
lookupForeign cid = do
  val <- gets (^? ix cid) >>= (?? IndexErr)
  case fromIpld val of
    Nothing -> throwError FailedIpldConversion
    Just i  -> pure i

writeForeign :: IsIpld a => a -> ForeignM Int Int Cid
writeForeign a = do
  let val = toIpld a
      cid = valueCid val
  modify (& ix cid .~ val)
  pure cid

liftBinaryOp
  :: IsIpld s
  => (s -> s -> s) -> (Spine Cid a b -> ForeignM a b (Tm Cid a b))
liftBinaryOp op [ForeignDataTm uid1, ForeignDataTm uid2] = do
  i <- op <$> lookupForeign uid1 <*> lookupForeign uid2
  ForeignDataTm <$> writeForeign i
liftBinaryOp _ _ = throwError FailedForeignFun

-- TODO: use QQ
exampleDataTypes :: DataTypeTable Cid String
exampleDataTypes = uIdMapFromList
  -- void has no constructor
  [ (voidUid, [])
  -- unit has a single nullary constructor
  , (unitUid, [[]])
  -- bool has two nullary constructors
  , (boolId, [[], []])
  -- `data Id a = Id a`
  , (idUid, [[VTy"a"]])
  -- A, B = D [R] | { C } | X
  , (valueTyUid, [
      -- [uidUid
    ])
  ]
