{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language LambdaCase #-}
{-# language StandaloneDeriving #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
module Interplanetary.Typecheck where

import Bound
import Control.Lens hiding ((??), from, to)
import Control.Monad (forM_)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Monoid ((<>))

import Interplanetary.Syntax
import Interplanetary.Util

data TcErr
  = DataUIdMismatch
  | ZipLengthMismatch
  | FailedDataTypeLookup
  | FailedConstructorLookup
  | AbilityUnification
  | TyUnification
  | LookupCommandTy
  | LookupVarTy
  | CantInfer TmI
  deriving (Eq, Show)

-- Read-only typing information
type DataTypeTable a = UIdMap (Vector (Vector (ValTy a)))
type InterfaceTable a = UIdMap (EffectInterface a)

-- * The data type table and interface table are global and never change
-- * The ability changes as we push in and pop out of rules
type TypingTables a = (DataTypeTable a, InterfaceTable a, Ability a)

-- Mutable typing information
--
-- This is mutable so we can solve for a type variable in some context and
-- carry the solution back out.
type TypingEnvVal a = Either (ValTy a) PolytypeS
newtype TypingEnv a = TypingEnv (Stack (TypingEnvVal a))

type instance IxValue (TypingEnv a) = TypingEnvVal a
type instance Index (TypingEnv a) = Int
instance Ixed (TypingEnv a) where
  ix k f (TypingEnv m) = TypingEnv <$> ix k f m

newtype TcM a b = TcM
  (ExceptT TcErr
  (StateT (TypingEnv a)
  (Reader (TypingTables a)))
  b)
  deriving (Functor, Applicative, Monad, MonadError TcErr)
deriving instance MonadState (TypingEnv a) (TcM a)
deriving instance MonadReader (TypingTables a) (TcM a)
type TcM' = TcM Int

runTcM :: TypingTables Int -> TypingEnv Int -> TcM' a -> Either TcErr a
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
  Value (Command uid row) -> do
    CommandDeclaration from to <- lookupCommandTy uid row
    ambient <- getAmbient
    pure $ SuspendedTy (CompTy from (Peg ambient to))
  Value (ForeignFun _uid _row) -> todo "infer ForeignFun"
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
check (Value (Lambda body)) (SuspendedTy (CompTy dom (Peg ability codom))) = do
  body' <- openWithTypes dom body
  withAbility ability $ check body' codom
-- DATA
check (Value (DataConstructor uid1 row tms)) (DataTy uid2 valTys) = do
  assert DataUIdMismatch (uid1 == uid2)
  argTys <- lookupConstructorTy uid1 row
  mapM_ (uncurry check) =<< strictZip ZipLengthMismatch tms argTys
-- CASE
check (Cut (Case uid1 rows) m) ty = do
  -- args :: (Vector (TyArg a))
  DataTy uid2 _args <- infer m
  assert DataUIdMismatch (uid1 == uid2)

  dataRows <- lookupDataType uid1 -- :: Vector (Vector ValTyI)
  zipped <- strictZip ZipLengthMismatch dataRows rows
  forM_ zipped $ \(dataConTys, rhs) -> do
    -- tys <- get
    let tys = todo "tys"
        rhs' = instantiate (tys !!) rhs
    withValTypes dataConTys (check rhs' ty)
-- HANDLE
check (Cut (Handle adj peg handlers fallthrouh) val) ty = do
  ambient <- getAmbient
  valTy <- withAbility (extendAbility ambient adj) (infer val)
  let adjTys = extendAbility emptyAbility adj
  forM_ adjTys (todo "check HANDLE")
-- LET
check (Cut (Let (Polytype binders valTy) body) val) ty = do
  todo "check LET"
  -- check val valTy
  -- check body ty
-- SWITCH
check m b = do
  a <- infer m
  _ <- unify a b ?? TyUnification
  pure ()

-- TODO: should we push these in this order?
withValTypes :: [ValTyI] -> TcM' a -> TcM' a
withValTypes tys = withState'
  (\(TypingEnv env) -> TypingEnv $ env <> (Left <$> tys))

-- | Get the types each data constructor holds for this data type.
--
-- Question: should this be parametrized by type parameters / abilities? IE do
-- we allow GADTs?
lookupDataType :: UId -> TcM' (Vector (Vector ValTyI))
lookupDataType uid = asks (^? _1 . ix uid) >>= (?? FailedDataTypeLookup)

lookupConstructorTy :: UId -> Row -> TcM' [ValTyI]
lookupConstructorTy uid row
  = asks (^? _1 . ix uid . ix row) >>= (?? FailedConstructorLookup)

lookupCommandTy :: UId -> Row -> TcM' (CommandDeclaration Int)
lookupCommandTy uid row
  = asks (^? _2 . ix uid . commands . ix row) >>= (?? LookupCommandTy)

openWithTypes :: [ValTyI] -> Scope Int (Tm Int) Int -> TcM' TmI
openWithTypes tys scope = withValTypes tys $
  pure $ instantiate Variable scope

withAbility :: AbilityI -> TcM' b -> TcM' b
withAbility ability action = local (& _3 .~ ability) action

getAmbient :: TcM' AbilityI
getAmbient = asks (^?! _3)

-- polyVarInstantiator :: [TyArg a] -> Int -> ValTy Int
-- polyVarInstantiator = _

-- lookupPolyVarTy :: v -> TcM' (Scope Int ValTy v)
-- lookupPolyVarTy = _

lookupVarTy :: Int -> TcM' ValTyI
lookupVarTy v = gets (^? ix v . _Left) >>= (?? LookupVarTy)
