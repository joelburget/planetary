{-# language DataKinds #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Library.HaskellForeign
  ( mkForeign
  , mkForeignTm
  , lookupForeign
  , writeForeign
  , haskellOracles
  , resolvedDecls
  , interfaceTable
  , intTy
  , boolTy
  , textTy
  , uidTy
  , vector
  , uidMap
  -- , lfix
  ) where

import Control.Lens hiding ((??), op)
import Control.Monad.Except
import Control.Monad.State
import Data.Monoid ((<>))
import Data.Text (Text)
import NeatInterpolation
import Network.IPLD as IPLD

import Planetary.Core
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser
import Planetary.Util

import Debug.Trace

haskellOracles :: Handlers
haskellOracles =
  [ (intOpsId, [ liftBinaryOp @Int (+) , liftBinaryOp @Int (-) ])
  , (boolOpsId, [ liftBinaryOp (&&) , liftBinaryOp (||), liftUnaryOp not ])
  , (textOpsId, [ liftBinaryOp @Text (<>) ])
  -- , (uidOpsId, [ generateUid ]
  , (fixOpsId, [ mkFix, unFix ])
  ]

intTy :: ValTyI
intTy = DataTy (UidTy intId) []

boolTy :: ValTyI
boolTy = DataTy (UidTy boolId) []

textTy :: ValTyI
textTy = DataTy (UidTy textId) []

uidTy :: ValTyI
uidTy = DataTy (UidTy uidId) []

vector, uidMap, lfix :: Vector TyArgI -> ValTyI

vector = DataTy (UidTy vectorId)
uidMap = DataTy (UidTy uidMapId)
lfix   = DataTy (UidTy lfixId)

-- For now these are all opaque: they don't expose any constructors we can see
-- XXX how do we check the types are saturated correctly?
-- haskellDataTypes :: DataTypeTableI
-- haskellDataTypes =
--   [ (vectorId, emptyDataTypeInterface)
--   , (uidMapId, emptyDataTypeInterface)
--   -- TODO: this kind is a bit of a lie since it's actually `* -> *`
--   , (lfixId, DataTypeInterface
--     [("f", ValTyK)]
--     [ConstructorDecl "Fix" (todo "arg tys") (todo "result tys")])
--   ]

-- TODO: some way to declare both implementation and type at the same time
-- interfaceTable :: InterfaceTableI
-- interfaceTable =
--   [ (intOpsId, EffectInterface []
--     [ CommandDeclaration "+" [intTy, intTy] intTy -- +
--     , CommandDeclaration "-" [intTy, intTy] intTy -- -
--     ])
--   , (boolOpsId, EffectInterface []
--     [ CommandDeclaration "&&" [boolTy, boolTy] boolTy -- &&
--     , CommandDeclaration "||" [boolTy, boolTy] boolTy -- ||
--     , CommandDeclaration "not" [boolTy]         boolTy -- not
--     ])
--   , (textOpsId, EffectInterface []
--     [ CommandDeclaration "concat" [textTy, textTy] textTy -- concat
--     ])
--   , (uidOpsId, EffectInterface []
--     [ CommandDeclaration "generateUid" [] uidTy -- generateUid
--     ])
--   , (fixOpsId, EffectInterface []
--     -- interface Fix F =
--     --   | fix   : F (Fix F) ->    Fix F
--     --   | unfix :    Fix F  -> F (Fix F)
--     [ CommandDeclaration "unfix" [
--         -- fix F -> F (fix F)
--         Polytype [("F", ValTyK)] (SuspendedTy (CompTy [
--     ])
--   ]

-- interfaceTable :: UIdMap Cid EffectInterfaceI
resolvedDecls :: ResolvedDecls
Right resolvedDecls = resolveDecls mempty $ forceDeclarations [text|
interface IntOps =
  | add : <Int> -> <Int> -> <Int>
  | sub : <Int> -> <Int> -> <Int>

interface BoolOps =
  | and : <Bool> -> <Bool> -> <Bool>
  | or  : <Bool> -> <Bool> -> <Bool>
  | not : <Bool> -> <Bool>

interface TextOps =
  | concat : <Text> -> <Text> -> <Text>

interface UidOps =
  | generateUid : <Uid>

interface FixOps =
  | mkFix : <F <Fix F>> ->    <Fix F>
  | unFix :    <Fix F>  -> <F <Fix F>>

-- TODO: these example data types don't really belong here

-- void has no constructor
data Void =

-- unit has a single nullary constructor
data Unit =
  | <unit>

-- bool has two nullary constructors
data Bool =
  | <true>
  | <false>

-- `data Id a = Id a`
data Id A =
  | <id A>
|]

interfaceTable :: InterfaceTableI
interfaceTable = _interfaces resolvedDecls

lookupForeign :: IsIpld a => Cid -> ForeignM a
lookupForeign cid = do
  db <- get
  val <- gets (^? ix cid) >>= (?? IndexErr)
  case fromIpld val of
    Nothing -> throwError FailedIpldConversion
    Just i  -> pure i

writeForeign :: IsIpld a => a -> ForeignM Cid
writeForeign a = do
  let val = toIpld a
      cid = valueCid val
  modify (& at cid ?~ val)
  pure cid

-- XXX
liftBinaryOp :: IsIpld s => (s -> s -> s) -> Handler
liftBinaryOp op [ForeignValue tyUid tySat uid1, ForeignValue _ _ uid2] env = do
  i <- op <$> lookupForeign uid1 <*> lookupForeign uid2
  i' <- writeForeign i
  pure (ForeignValue tyUid tySat i', env)
liftBinaryOp _ _ _ = throwError FailedForeignFun

-- XXX
liftUnaryOp :: IsIpld s => (s -> s) -> Handler
liftUnaryOp op [ForeignValue tyUid tySat uid] env = do
  i <- op <$> lookupForeign uid
  i' <- writeForeign i
  pure (ForeignValue tyUid tySat i', env)
liftUnaryOp _ _ _ = throwError FailedForeignFun

mkFix :: Handler
mkFix [a] env = do
  traceM $ "running mkfix on: " ++ show a
  a' <- writeForeign a
  traceM $ "mkfix returning: " ++ show a'
  pure (ForeignValue lfixId [{- XXX -}] a', env)

unFix :: Handler
-- unFix [ForeignValue uid [val] tyUid]
unFix [ForeignValue tyUid _vals valUid] env
  | tyUid == lfixId = do
    traceM "running unfix"
    val <- lookupForeign valUid
    traceM $ "unfix returning: " ++ show val
    pure (val, env)
unFix x _stk = traceShowM x >> throwError FailedForeignFun

mkForeign :: IsIpld a => a -> (Cid, IPLD.Value)
mkForeign val = let val' = toIpld val in (valueCid val', val')

mkForeignTm :: IsIpld a => Cid -> Vector ValTyI -> a -> TmI
mkForeignTm tyId tySat = ForeignValue tyId tySat . fst . mkForeign
