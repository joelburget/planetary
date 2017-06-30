{-# language DataKinds #-}
{-# language OverloadedStrings #-}
{-# language TypeApplications #-}
module Planetary.Library.HaskellForeign
  ( mkForeign
  , mkForeignTm
  , lookupForeign
  , writeForeign
  , haskellOracles
  , interfaceTable
  , intTy
  , textTy
  , uidTy
  , haskellDataTypes
  , vector
  , uidMap
  -- , lfix
  ) where

import Control.Lens hiding ((??), op)
import Control.Monad.Except
import Control.Monad.State
import Data.Monoid ((<>))
import Data.Text (Text)
import Network.IPLD as IPLD

import Planetary.Core
import Planetary.Support.Ids
import Planetary.Util

haskellOracles :: CurrentHandlers
haskellOracles = uIdMapFromList
  [ (intOpsId, [ liftBinaryOp @Int (+) , liftBinaryOp @Int (-) ])
  , (boolOpsId, [ liftBinaryOp (&&) , liftBinaryOp (||), liftUnaryOp not ])
  , (textOpsId, [ liftBinaryOp @Text (<>) ])
  -- , (uidOpsId, [ generateUid ]
  ]

intTy :: ValTyI
intTy = DataTy intId []

boolTy :: ValTyI
boolTy = DataTy boolId []

textTy :: ValTyI
textTy = DataTy textId []

uidTy :: ValTyI
uidTy = DataTy uidId []

vector, uidMap, lfix :: Vector TyArgI -> ValTyI

vector = DataTy vectorId
uidMap = DataTy uidMapId
lfix   = DataTy lfixId

-- For now these are all opaque: they don't expose any constructors we can see
-- XXX how do we check the types are saturated correctly?
haskellDataTypes :: DataTypeTableI
haskellDataTypes = uIdMapFromList
  [ (vectorId, emptyDataTypeInterface)
  , (uidMapId, emptyDataTypeInterface)
  -- , (lfixId, DataTypeInterface ["Fix"] [])
  ]

-- TODO: some way to declare both implementation and type at the same time
interfaceTable :: InterfaceTableI
interfaceTable = uIdMapFromList
  [ (intOpsId, EffectInterface []
    [ CommandDeclaration "+" [intTy, intTy] intTy -- +
    , CommandDeclaration "-" [intTy, intTy] intTy -- -
    ])
  , (boolOpsId, EffectInterface []
    [ CommandDeclaration "&&" [boolTy, boolTy] boolTy -- &&
    , CommandDeclaration "||" [boolTy, boolTy] boolTy -- ||
    , CommandDeclaration "not" [boolTy]         boolTy -- not
    ])
  , (textOpsId, EffectInterface []
    [ CommandDeclaration "concat" [textTy, textTy] textTy -- concat
    ])
  , (uidOpsId, EffectInterface []
    [ CommandDeclaration "generateUid" [] uidTy -- generateUid
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

-- XXX
liftBinaryOp
  :: IsIpld s
  => (s -> s -> s) -> (Spine Cid b -> ForeignM (Tm 'TM Cid b))
liftBinaryOp op [ForeignTm tyUid tySat uid1, ForeignTm _ _ uid2] = do
  i <- op <$> lookupForeign uid1 <*> lookupForeign uid2
  ForeignTm tyUid tySat <$> writeForeign i
liftBinaryOp _ _ = throwError FailedForeignFun

-- XXX
liftUnaryOp
  :: IsIpld s
  => (s -> s) -> (Spine Cid b -> ForeignM (Tm 'TM Cid b))
liftUnaryOp op [ForeignTm tyUid tySat uid] = do
  i <- op <$> lookupForeign uid
  ForeignTm tyUid tySat <$> writeForeign i
liftUnaryOp _ _ = throwError FailedForeignFun

mkForeign :: IsIpld a => a -> (Cid, IPLD.Value)
mkForeign val = let val' = toIpld val in (valueCid val', val')

mkForeignTm :: IsIpld a => Cid -> Vector ValTyI -> a -> TmI
mkForeignTm tyId tySat = ForeignTm tyId tySat . fst . mkForeign

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
