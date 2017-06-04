{-# language TypeApplications #-}
module Planetary.Library.HaskellForeign where

import Control.Lens hiding ((??), op)
import Control.Monad.Except
import Control.Monad.State
import Network.IPLD as IPLD

import Planetary.Core
import Planetary.Support.Ids
import Planetary.Util

haskellOracles :: CurrentHandlers
haskellOracles = uIdMapFromList
  [ (intOpsId, [ liftBinaryOp @Int (+) , liftBinaryOp @Int (-) ])
  , (boolOpsId, [ liftBinaryOp (&&) , liftBinaryOp (||), liftUnaryOp not ])
  , (strOpsId, [ liftBinaryOp @String (++) ])
  -- , (uidOpsId, [ generateUid ]
  ]

intTy :: ValTyI
intTy = DataTy intId []

boolTy :: ValTyI
boolTy = DataTy boolId []

strTy :: ValTyI
strTy = DataTy strId []

uidTy :: ValTyI
uidTy = DataTy uidId []

vector, uidMap, lfix :: Vector TyArgI -> ValTyI

vector = DataTy vectorId
uidMap = DataTy uidMapId
lfix   = DataTy lfixId

-- For now these are all opaque: they don't expose any constructors we can see
-- XXX how do we check the types are saturated correctly?
dataTypes :: DataTypeTableI
dataTypes = uIdMapFromList
  [ (vectorId, [])
  , (uidMapId, [])
  , (lfixId, [])
  ]

-- TODO: some way to declare both implementation and type at the same time
interfaceTable :: InterfaceTableI
interfaceTable = uIdMapFromList
  [ (intOpsId, EffectInterface []
    [ CommandDeclaration [intTy, intTy] intTy -- +
    , CommandDeclaration [intTy, intTy] intTy -- -
    ])
  , (boolOpsId, EffectInterface []
    [ CommandDeclaration [boolTy, boolTy] boolTy -- &&
    , CommandDeclaration [boolTy, boolTy] boolTy -- ||
    , CommandDeclaration [boolTy]         boolTy -- not
    ])
  , (strOpsId, EffectInterface []
    [ CommandDeclaration [strTy, strTy] strTy -- concat
    ])
  , (uidOpsId, EffectInterface []
    [ CommandDeclaration [] uidTy -- generateUid
    ])
  ]

lookupForeign :: IsIpld a => Cid -> ForeignM a
lookupForeign cid = do
  val <- gets (^? ix cid) >>= (?? IndexErr)
  case fromIpld val of
    Nothing -> throwError FailedIpldConversion
    Just i  -> pure i

writeForeign :: IsIpld a => a -> ForeignM Cid
writeForeign a = do
  let val = toIpld a
      cid = valueCid val
  modify (& ix cid .~ val)
  pure cid

liftBinaryOp
  :: IsIpld s
  => (s -> s -> s) -> (Spine Cid a b -> ForeignM (Tm Cid a b))
liftBinaryOp op [ForeignDataTm uid1, ForeignDataTm uid2] = do
  i <- op <$> lookupForeign uid1 <*> lookupForeign uid2
  ForeignDataTm <$> writeForeign i
liftBinaryOp _ _ = throwError FailedForeignFun

liftUnaryOp
  :: IsIpld s
  => (s -> s) -> (Spine Cid a b -> ForeignM (Tm Cid a b))
liftUnaryOp op [ForeignDataTm uid] = do
  i <- op <$> lookupForeign uid
  ForeignDataTm <$> writeForeign i
liftUnaryOp _ _ = throwError FailedForeignFun

mkForeign :: IsIpld a => a -> (Cid, IPLD.Value)
mkForeign val = let val' = toIpld val in (valueCid val', val')

mkForeignTm :: IsIpld a => a -> TmI
mkForeignTm = ForeignDataTm . fst . mkForeign

-- -- TODO: use QQ
-- exampleDataTypes :: DataTypeTable Cid String
-- exampleDataTypes = uIdMapFromList
--   -- void has no constructor
--   [ (voidUid, [])
--   -- unit has a single nullary constructor
--   , (unitId, [[]])
--   -- bool has two nullary constructors
--   , (boolId, [[], []])
--   -- `data Id a = Id a`
--   , (idUid, [[VTy"a"]])
--   -- A, B = D [R] | { C } | X
--   , (valueTyUid, [
--       -- [uidUid
--     ])
--   ]
