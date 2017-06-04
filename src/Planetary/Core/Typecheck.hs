{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language LambdaCase #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
module Planetary.Core.Typecheck where

import Bound
import Control.Lens hiding ((??), from, to)
import Control.Monad (forM_)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.HashMap.Lazy (intersectionWith)
import Data.Monoid ((<>))
import Network.IPLD hiding (Row)

import Planetary.Core.Syntax
import Planetary.Core.Syntax.Patterns
import Planetary.Core.UIdMap
import Planetary.Util

data TcErr
  = DataUIdMismatch Cid Cid
  | ZipLengthMismatch
  | FailedDataTypeLookup
  | FailedConstructorLookup
  | AbilityUnification
  | TyUnification
  | LookupCommands
  | LookupCommandTy
  | LookupVarTy
  | CantInfer TmI
  | NotClosed
  deriving (Eq, Show)

-- Read-only typing information
-- TODO: why does DataTypeTable not hold `DataTypeInterface`s?
type DataTypeTable  uid a = UIdMap uid (Vector (Vector (ValTy uid a)))
type InterfaceTable uid a = UIdMap uid (EffectInterface uid a)

-- * The data type table and interface table are global and never change
-- * The ability changes as we push in and pop out of rules
type TypingTables uid a = (DataTypeTable uid a, InterfaceTable uid a, Ability uid a)

-- Mutable typing information
--
-- This is mutable so we can solve for a type variable in some context and
-- carry the solution back out.
type TypingEnvVal uid a = Either (ValTy uid a) PolytypeI
newtype TypingEnv uid a = TypingEnv (Stack (TypingEnvVal uid a))

type instance IxValue (TypingEnv uid a) = TypingEnvVal uid a
type instance Index (TypingEnv uid a) = Int
instance Ixed (TypingEnv uid a) where
  ix k f (TypingEnv m) = TypingEnv <$> ix k f m

newtype TcM uid a b = TcM
  (ExceptT TcErr
  (StateT (TypingEnv uid a)
  (Reader (TypingTables uid a)))
  b)
  deriving (Functor, Applicative, Monad, MonadError TcErr)
deriving instance MonadState (TypingEnv uid a) (TcM uid a)
deriving instance MonadReader (TypingTables uid a) (TcM uid a)

type DataTypeTableI  = DataTypeTable  Cid Int
type InterfaceTableI = InterfaceTable Cid Int
type TypingTablesI   = TypingTables   Cid Int
type TypingEnvI      = TypingEnv      Cid Int
type TcM'            = TcM            Cid Int

runTcM
  :: TypingTablesI
  -> TypingEnvI
  -> TcM' a
  -> Either TcErr a
runTcM tables env (TcM action) = runReader
  (evalStateT
    (runExceptT action)
    env
  )
  tables

infer :: TmI -> TcM' ValTyI
infer = \case
  -- VAR
  Variable v -> lookupVarTy v
  -- POLYVAR
  InstantiatePolyVar _v _tys -> todo "infer polyvar"
    -- p <- lookupPolyVarTy v
    -- pure $ instantiate (polyVarInstantiator tys) p
  -- COMMAND
  Value (Command uid row spine) -> do
    CommandDeclaration from to <- lookupCommandTy uid row
    ambient <- getAmbient
    pure $ SuspendedTy (CompTy from (Peg ambient to))
  -- APP
  Cut (Application spine) f -> do
    SuspendedTy (CompTy dom (Peg ability retTy)) <- infer f
    ambient <- getAmbient
    _ <- unify ability ambient ?? AbilityUnification
    _ <- mapM_ (uncurry check) =<< strictZip ZipLengthMismatch spine dom
    pure retTy
  -- COERCE
  Annotation n a -> check (Value n) a >> pure a
  x -> throwError (CantInfer x)

check :: TmI -> ValTyI -> TcM' ()
-- FUN
check (Value (Lambda _binders body))
      (SuspendedTy (CompTy dom (Peg ability codom))) = do
  body' <- openWithTypes dom body
  withAbility ability $ check body' codom
-- DATA
check (Value (DataConstructor uid1 row tms)) (DataTy uid2 valTys) = do
  assert (DataUIdMismatch uid1 uid2) (uid1 == uid2)
  argTys <- lookupConstructorTy uid1 row
  mapM_ (uncurry check) =<< strictZip ZipLengthMismatch tms argTys
-- CASE
check (Cut (Case uid1 rows) m) ty = do
  -- args :: (Vector (TyArg a))
  DataTy uid2 _args <- infer m
  assert (DataUIdMismatch uid1 uid2) (uid1 == uid2)

  dataRows <- lookupDataType uid1 -- :: Vector (Vector ValTyI)
  zipped <- strictZip ZipLengthMismatch dataRows rows
  forM_ zipped $ \(dataConTys, (_, rhs)) ->
    withValTypes' dataConTys rhs (`check` ty)
-- HANDLE
check (Cut (Handle adj peg (AdjustmentHandlers handlers) fallthrough) val) ty = do
  ambient <- getAmbient
  valTy <- withAbility (extendAbility ambient adj) (infer val)
  cmds <- instantiateAbility $ extendAbility emptyAbility adj
  pairs <- uidZip handlers cmds
  forMOf_ (traverse . traverse) pairs $ \(handler, CommandDeclaration as b) ->
    openAdjustmentHandler handler as (CompTy [b] (Peg ambient valTy)) $ \tm ->
      check tm ty
  withValTypes [valTy] $
    let fallthrough' = succOpen fallthrough
    in check fallthrough' ty
-- LET
check (Cut (Let pty _name body) val) ty = do
  valTy <- instantiateWithEnv pty
  check val valTy
  withPolyty pty $ check (succOpen body) ty
-- SWITCH
check m b = do
  a <- infer m
  _ <- unify a b ?? TyUnification
  pure ()

-- TODO: convert to `fromScope`?
-- TODO: is the succ necessary?
succOpen :: Scope () (Tm Cid Int) Int -> TmI
succOpen = (succ <$>) . instantiate1 (V 0)

instantiateAbility :: AbilityI -> TcM' (UIdMap Cid [CommandDeclarationI])
instantiateAbility (Ability _ uidmap) =
  iforM uidmap $ \uid tyArgs -> lookupCommands uid
    -- iforM cmds $ \row (CommandDeclaration as b) ->
    --   -- TODO should we be unifying the args and as? what's wrong here?
    --   todo "instantiateAbility" tyArgs as b

instantiateWithEnv :: PolytypeI -> TcM' ValTyI
instantiateWithEnv = todo "instantiateWithEnv"

uidZip
  :: MonadError TcErr m
  => UIdMap Cid [a]
  -> UIdMap Cid [b]
  -> m (UIdMap Cid [(a, b)])
uidZip (UIdMap as) (UIdMap bs) = UIdMap <$>
  sequence (intersectionWith (strictZip ZipLengthMismatch) as bs)

-- TODO: should we push these in this order?
-- * we should reverse and push at the head
withValTypes :: [ValTyI] -> TcM' a -> TcM' a
withValTypes tys = withState'
  (\(TypingEnv env) -> TypingEnv $ env <> (Left <$> tys))

-- TODO: these next two functions seem the same?
withValTypes'
  :: [ValTyI]
  -> Scope Int (Tm Cid Int) Int
  -> (TmI -> TcM' a)
  -> TcM' a
withValTypes' tys scope cb =
  let body = instantiate V scope
  in withValTypes tys (cb body)

openWithTypes :: [ValTyI] -> Scope Int (Tm Cid Int) Int -> TcM' TmI
openWithTypes tys scope = withValTypes tys $
  pure $ instantiate V scope

openAdjustmentHandler
  :: Scope (Maybe Int) (Tm Cid Int) Int
  -> [ValTyI]
  -> CompTyI
  -> (TmI -> TcM' a)
  -> TcM' a
openAdjustmentHandler handler argTys handlerTy cb =
  let envAdj (TypingEnv env) = TypingEnv $
        (Left <$> argTys) <> ((Left $ SuspendedTy handlerTy):env)

      instantiator Nothing  = V 0
      instantiator (Just i) = V (length argTys + 1)

  in withState' envAdj (cb (instantiate instantiator handler))

withPolyty :: PolytypeI -> TcM' a -> TcM' a
withPolyty pty = withState'
  (\(TypingEnv env) -> TypingEnv $ env <> [Right pty])

-- | Get the types each data constructor holds for this data type.
--
-- Question: should this be parametrized by type parameters / abilities? IE do
-- we allow GADTs?
lookupDataType :: Cid -> TcM' (Vector (Vector ValTyI))
lookupDataType uid = asks (^? _1 . ix uid) >>= (?? FailedDataTypeLookup)

lookupConstructorTy :: Cid -> Row -> TcM' [ValTyI]
lookupConstructorTy uid row
  = asks (^? _1 . ix uid . ix row) >>= (?? FailedConstructorLookup)

lookupCommands :: Cid -> TcM' [CommandDeclarationI]
lookupCommands uid = asks (^? _2 . ix uid . commands) >>= (?? LookupCommands)

lookupCommandTy :: Cid -> Row -> TcM' CommandDeclarationI
lookupCommandTy uid row
  = asks (^? _2 . ix uid . commands . ix row) >>= (?? LookupCommandTy)

withAbility :: AbilityI -> TcM' b -> TcM' b
withAbility ability = local (& _3 .~ ability)

getAmbient :: TcM' AbilityI
getAmbient = asks (^?! _3)

-- polyVarInstantiator :: [TyArg a] -> Int -> ValTy Int
-- polyVarInstantiator = _

-- lookupPolyVarTy :: v -> TcM' (Scope Int ValTy v)
-- lookupPolyVarTy = _

lookupVarTy :: Int -> TcM' ValTyI
lookupVarTy v = gets (^? ix v . _Left) >>= (?? LookupVarTy)
