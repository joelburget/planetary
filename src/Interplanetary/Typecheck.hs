{-# language LambdaCase #-}
{-# language TypeOperators #-}
module Interplanetary.Typecheck where

-- import Control.Unification

import Bound
import Control.Lens hiding ((??))
import Control.Monad (forM_)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Control.Unification

import Interplanetary.Syntax
import Interplanetary.Util

data TcErr
  = DataUidMismatch
  | ZipLengthMismatch
  | FailedDataTypeLookup
  | FailedConstructorLookup

-- Mutable typing information
data TypingEnv a = TypingEnv (Stack (Either (ValTy a) PolytypeS))

newtype TcM a b = TcM
  (ExceptT TcErr
  (StateT (TypingEnv a)
  (Reader (Ability a, TypingTables a)))
  b)
  deriving (Functor, Applicative, Monad, MonadError TcErr)
instance MonadState (TypingEnv a) (TcM a) where
instance MonadReader (Ability a, TypingTables a) (TcM a) where
type TcM' = TcM Int

runTcM :: (Ability Int, TypingTables Int) -> TypingEnv Int -> TcM' a -> Either TcErr a
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
  InstantiatePolyVar v tys -> do
    p <- lookupPolyVarTy v
    pure $ instantiate (polyVarInstantiator tys) p
  -- COMMAND
  Value (Command uid row) -> SuspendedTy <$> lookupCommandTy uid row
  -- APP
  Cut (Application spine) f -> do
    SuspendedTy (CompTy dom (Peg ability retTy)) <- infer f
    ambient <- ambientAbility
    _ <- unifyAbility ability ambient
    _ <- mapM_ (uncurry check) =<< strictZip ZipLengthMismatch spine dom
    pure retTy
  -- COERCE
  Annotation n a -> check (Value n) a >> pure a

check :: TmI -> ValTyI -> TcM' ()
-- FUN
check (Value (Lambda body)) (SuspendedTy (CompTy dom (Peg ability codom))) = do
  body' <- openWithTypes dom body
  withAbility ability $ check body' codom
-- DATA
check (Value (DataConstructor uid1 row values)) (DataTy uid2 valTys) = do
  assert DataUidMismatch (uid1 == uid2)
  argTys <- lookupConstructorTy uid1 row
  let tms = Value <$> values
  mapM_ (uncurry check) =<< strictZip ZipLengthMismatch tms argTys
-- CASE
check (Cut (Case _uid rows) m) ty = do
  -- TODO: check uids match?
  DataTy uid args <- infer m
  dataRows <- lookupDataType uid
  zipped <- strictZip ZipLengthMismatch dataRows rows
  forM_ zipped $ \(dataConTys, rhs) -> todo "check CASE"
    -- withValTypes dataConTys (check rhs ty)
-- HANDLE
check (Cut (Handle adj peg handlers fallthrouh) val) ty = do
  ambient <- ambientAbility
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
  unifyTy a b
  pure ()

-- | Get the types each data constructor holds for this data type.
--
-- Question: should this be parametrized by type parameters / abilities? IE do
-- we allow GADTs?
lookupDataType :: Uid -> TcM' (Vector (Vector ValTyI))
lookupDataType uid = asks (^? _2 . _1 . ix uid) >>= (?? FailedDataTypeLookup)

lookupConstructorTy :: Uid -> Row -> TcM' [ValTyI]
lookupConstructorTy uid row
  = asks (^? _2 . _1 . ix uid . ix row) >>= (?? FailedConstructorLookup)

openWithTypes :: [ValTyI] -> Scope Int (Tm Int) Int -> TcM' TmI
openWithTypes tys scope = do
  -- TODO add to a lookup table
  pure $ instantiate Variable scope

withAbility :: AbilityI -> TcM' b -> TcM' b
withAbility ability action = local (& _1 .~ ability) action

ambientAbility :: TcM' AbilityI
ambientAbility = asks (^?! _1)

unifyAbility :: AbilityI -> AbilityI -> TcM' AbilityI
unifyAbility ab1 ab2 = do
  unify (UTerm ab1) (UTerm ab2)

unifyTy :: ValTy v -> ValTy v -> TcM' (ValTy v)
unifyTy = _

polyVarInstantiator :: [TyArg a] -> Int -> ValTy Int
polyVarInstantiator = _

lookupPolyVarTy :: v -> TcM' (Scope Int ValTy v)
lookupPolyVarTy = _

lookupVarTy :: v -> TcM' (ValTy v)
lookupVarTy = _

lookupCommandTy :: Uid -> Row -> TcM' CompTyI
lookupCommandTy = _
