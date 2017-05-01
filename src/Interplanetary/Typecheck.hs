{-# language FlexibleContexts #-}
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
import Data.HashMap.Lazy (intersectionWith)
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
  | LookupCommands
  | LookupCommandTy
  | LookupVarTy
  | CantInfer TmI
  | NotClosed
  deriving (Eq, Show)

-- Read-only typing information
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
type TcM' = TcM UId Int

runTcM
  :: TypingTables UId Int
  -> TypingEnv UId Int
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
  Value (Command uid row) -> do
    CommandDeclaration from to <- lookupCommandTy uid row
    ambient <- getAmbient
    pure $ SuspendedTy (CompTy from (Peg ambient to))
  Value (ForeignFun uid row) -> do
    -- TODO:
    -- Again, I wonder whether ForeignFun and Command are exactly the same.
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
  forM_ zipped $ \(dataConTys, rhs) ->
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
    let fallthrough' = instantiate1 (V 0) fallthrough
    in check fallthrough' ty
-- LET
check (Cut (Let pty body) val) ty = do
  valTy <- instantiateWithEnv pty
  check val valTy
  withPolyty pty $ check (instantiate1 (V 0) body) ty
-- SWITCH
check m b = do
  a <- infer m
  _ <- unify a b ?? TyUnification
  pure ()

instantiateAbility :: AbilityI -> TcM' (UIdMap UId [CommandDeclaration UId Int])
instantiateAbility (Ability _ uidmap) = do
  iforM uidmap $ \uid tyArgs -> lookupCommands uid
    -- iforM cmds $ \row (CommandDeclaration as b) ->
    --   -- TODO should we be unifying the args and as? what's wrong here?
    --   todo "instantiateAbility" tyArgs as b

instantiateWithEnv :: PolytypeI -> TcM' ValTyI
instantiateWithEnv = todo "instantiateWithEnv"

uidZip
  :: MonadError TcErr m
  => UIdMap UId [a]
  -> UIdMap UId [b]
  -> m (UIdMap UId [(a, b)])
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
  -> Scope Int (Tm UId Int) Int
  -> (TmI -> TcM' a)
  -> TcM' a
withValTypes' tys scope cb =
  let body = instantiate V scope
  in withValTypes tys (cb body)

openWithTypes :: [ValTyI] -> Scope Int (Tm UId Int) Int -> TcM' TmI
openWithTypes tys scope = withValTypes tys $
  pure $ instantiate V scope

openAdjustmentHandler
  :: Scope (Maybe Int) (Tm UId Int) Int
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
lookupDataType :: UId -> TcM' (Vector (Vector ValTyI))
lookupDataType uid = asks (^? _1 . ix uid) >>= (?? FailedDataTypeLookup)

lookupConstructorTy :: UId -> Row -> TcM' [ValTyI]
lookupConstructorTy uid row
  = asks (^? _1 . ix uid . ix row) >>= (?? FailedConstructorLookup)

lookupCommands :: UId -> TcM' [CommandDeclaration UId Int]
lookupCommands uid = asks (^? _2 . ix uid . commands) >>= (?? LookupCommands)

lookupCommandTy :: UId -> Row -> TcM' (CommandDeclaration UId Int)
lookupCommandTy uid row
  = asks (^? _2 . ix uid . commands . ix row) >>= (?? LookupCommandTy)

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
