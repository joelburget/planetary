{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language LambdaCase #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
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
  | FailedConstructorLookup Cid Row
  | AbilityUnification
  | TyUnification ValTyI ValTyI
  | LookupCommands
  | LookupCommandTy
  | LookupVarTy Int
  | CantInfer TmI
  | NotClosed
  deriving (Eq, Show)

-- Read-only typing information
type DataTypeTable  uid a = UIdMap uid (DataTypeInterface uid a)
type InterfaceTable uid a = UIdMap uid (EffectInterface uid a)

-- * The data type table and interface table are global and never change
-- * The ability changes as we push in and pop out of rules
data TypingEnv uid a = TypingEnv
  { _typingData       :: DataTypeTable  uid a
  , _typingInterfaces :: InterfaceTable uid a
  , _typingAbilities  :: Ability        uid a
  } deriving Show

makeLenses ''TypingEnv

-- Mutable typing information
--
-- This is mutable so we can solve for a type variable in some context and
-- carry the solution back out.
type TypingStateEntry uid a = Either (ValTy uid a) PolytypeI
newtype TypingState uid a = TypingState (Stack (TypingStateEntry uid a))

type instance IxValue (TypingState uid a) = TypingStateEntry uid a
type instance Index (TypingState uid a) = Int
instance Ixed (TypingState uid a) where
  ix k f (TypingState m) = TypingState <$> ix k f m

newtype TcM uid a b = TcM
  (ExceptT TcErr
  (StateT (TypingState uid a)
  (Reader (TypingEnv uid a)))
  b)
  deriving (Functor, Applicative, Monad, MonadError TcErr)
deriving instance MonadState (TypingState uid a) (TcM uid a)
deriving instance MonadReader (TypingEnv uid a) (TcM uid a)

type DataTypeTableI  = DataTypeTable  Cid Int
type InterfaceTableI = InterfaceTable Cid Int
type TypingEnvI      = TypingEnv      Cid Int
type TypingStateI    = TypingState    Cid Int
type TcM'            = TcM            Cid Int

runTcM
  :: TypingEnvI
  -> TypingStateI
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
  -- APP
  Cut (Application spine) f -> do
    SuspendedTy (CompTy dom (Peg ability retTy)) <- infer f
    ambient <- getAmbient
    _ <- unify ability ambient ?? AbilityUnification
    _ <- mapM_ (uncurry check) =<< strictZip ZipLengthMismatch spine dom
    pure retTy
  -- COERCE
  Annotation n a -> check (Value n) a >> pure a

  ForeignTm uid sat _ -> pure (DataTy uid (TyArgVal <$> sat))
  x -> throwError (CantInfer x)

check :: TmI -> ValTyI -> TcM' ()
-- FUN
check (Value (Lambda _binders body))
      (SuspendedTy (CompTy dom (Peg ability codom))) = do
  withValTypes' dom body $ \body' ->
    withAbility ability $
      check body' codom
-- DATA
check (Value (DataConstructor uid1 row tms)) (DataTy uid2 valTys) = do
  assert (DataUIdMismatch uid1 uid2) (uid1 == uid2)
  ConstructorDecl _name argTys <- lookupConstructorTy uid1 row
  mapM_ (uncurry check) =<< strictZip ZipLengthMismatch tms argTys
-- CASE
check (Cut (Case uid1 rows) m) ty = do
  -- args :: (Vector (TyArg a))
  DataTy uid2 _args <- infer m
  assert (DataUIdMismatch uid1 uid2) (uid1 == uid2)

  dataRows <- dataInterface <$> lookupDataType uid1 -- :: Vector (Vector ValTyI)
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
  _ <- unify a b ?? TyUnification a b
  pure ()

dataInterface :: DataTypeInterface uid a -> Vector (Vector (ValTy uid a))
dataInterface (DataTypeInterface _ ctors) =
  let f (ConstructorDecl _name args) = args
  in f <$> ctors

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
  (\(TypingState env) -> TypingState $ env <> (Left <$> tys))

withValTypes'
  :: [ValTyI]
  -> Scope Int (Tm Cid Int) Int
  -> (TmI -> TcM' a)
  -> TcM' a
withValTypes' tys scope cb =
  let body = instantiate V scope
  in withValTypes tys (cb body)

openAdjustmentHandler
  :: Scope (Maybe Int) (Tm Cid Int) Int
  -> [ValTyI]
  -> CompTyI
  -> (TmI -> TcM' a)
  -> TcM' a
openAdjustmentHandler handler argTys handlerTy cb =
  let envAdj (TypingState env) = TypingState $
        (Left <$> argTys) <> ((Left $ SuspendedTy handlerTy):env)

      instantiator Nothing  = V 0
      instantiator (Just i) = V (length argTys + 1)

  in withState' envAdj (cb (instantiate instantiator handler))

withPolyty :: PolytypeI -> TcM' a -> TcM' a
withPolyty pty = withState'
  (\(TypingState env) -> TypingState $ env <> [Right pty])

-- | Get the types each data constructor holds for this data type.
--
-- Question: should this be parametrized by type parameters / abilities? IE do
-- we allow GADTs?
lookupDataType :: Cid -> TcM' DataTypeInterfaceI
lookupDataType uid
  = asks (^? typingData . ix uid)
    >>= (?? FailedDataTypeLookup)

lookupConstructorTy :: Cid -> Row -> TcM' ConstructorDeclI
lookupConstructorTy uid row
  = do  env <- ask
        asks (^? typingData . ix uid . constructors . ix row)
          >>= (?? FailedConstructorLookup uid row)

lookupCommands :: Cid -> TcM' [CommandDeclarationI]
lookupCommands uid
  = asks (^? typingInterfaces . ix uid . commands)
    >>= (?? LookupCommands)

lookupCommandTy :: Cid -> Row -> TcM' CommandDeclarationI
lookupCommandTy uid row
  = asks (^? typingInterfaces . ix uid . commands . ix row)
    >>= (?? LookupCommandTy)

withAbility :: AbilityI -> TcM' b -> TcM' b
withAbility ability = local (& typingAbilities .~ ability)

getAmbient :: TcM' AbilityI
getAmbient = asks (^?! typingAbilities)

-- polyVarInstantiator :: [TyArg a] -> Int -> ValTy Int
-- polyVarInstantiator = _

-- lookupPolyVarTy :: v -> TcM' (Scope Int ValTy v)
-- lookupPolyVarTy = _

lookupVarTy :: Int -> TcM' ValTyI
lookupVarTy v = gets (^? ix v . _Left) >>= (?? LookupVarTy v)
