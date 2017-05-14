{-# language DataKinds #-}
{-# language DeriveDataTypeable #-}
{-# language DeriveFoldable #-}
{-# language DeriveFunctor #-}
{-# language DeriveGeneric #-}
{-# language DeriveTraversable #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language KindSignatures #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms #-}
{-# language Rank2Types #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
{-# language TypeFamilies #-}
module Interplanetary.Syntax
  ( module Interplanetary.Syntax
  , module Interplanetary.UIdMap
  ) where

import Bound
import Control.Lens.Plated
import Control.Lens.TH (makeLenses)
import Control.Monad (ap, zipWithM)
import Data.Data
import Data.Data.Lens
import Data.Foldable (toList)
import Data.Functor.Classes
import Data.List (elemIndex)
import Data.Monoid ((<>))
import GHC.Generics
import Network.IPLD hiding (Value, Row)

import Interplanetary.Util
import Interplanetary.UIdMap

-- TODO:
-- * Right now we use simple equality to check types but should implement
--   unification
-- * Be more granular about the capabilities each function needs instead of
--   hardcoding its monad.
-- * Error messaging is pitiful
--   - show some sort of helpful info
--   - our errors are essentially meaningless
-- * Should type and effect variables share a namespace?

type Row = Int

-- Types

data ValTy uid a
  = DataTy uid (Vector (TyArg uid a))
  | SuspendedTy (CompTy uid a)
  | VariableTy a
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

instance (IsUid uid, Data uid, Data a) => Plated (ValTy uid a) where
  plate = uniplate

data CompTy uid a = CompTy
  { compDomain :: Vector (ValTy uid a)
  , compCodomain :: Peg uid a
  } deriving (Eq, Show, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

instance (IsUid uid, Data uid, Data a) => Plated (CompTy uid a) where
  plate = uniplate

data Peg uid a = Peg
  { pegAbility :: Ability uid Int
  , pegVal :: ValTy uid a
  } deriving (Eq, Show, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

instance (IsUid uid, Data uid, Data a) => Plated (Peg uid a) where
  plate = uniplate

data TyArg uid a
  = TyArgVal (ValTy uid a)
  | TyArgAbility (Ability uid Int)
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

data Kind = ValTy | EffTy
  deriving (Show, Eq, Ord, Typeable, Data, Generic)

data Polytype uid a = Polytype
  -- Universally quantify over a bunch of variables
  { polyBinders :: Vector Kind
  -- resulting in a value type
  , polyVal :: Scope Int (ValTy uid) a
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

polytype :: Eq a => Vector (a, Kind) -> ValTy uid a -> Polytype uid a
polytype binders body =
  let (names, kinds) = unzip binders
  in Polytype kinds (abstract (`elemIndex` names) body)

newtype ConstructorDecl uid a = ConstructorDecl (Vector (ValTy uid a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

-- A collection of data constructor signatures (which can refer to bound type /
-- effect variables).
data DataTypeInterface uid a = DataTypeInterface
  -- we universally quantify over some number of type variables
  { dataBinders :: Vector (a, Kind)
  -- a collection of constructors taking some arguments
  , constructors :: Vector (ConstructorDecl uid a)
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

instance IsIpld (DataTypeInterface Cid Int) where -- XXX
instance IsIpld (EffectInterface Cid Int) where -- XXX

instance (IsUid uid, Data uid, Data a) => Plated (DataTypeInterface uid a) where
  plate = todo "plate DataTypeInterface"

dataInterface :: DataTypeInterface uid a -> Vector (Vector (ValTy uid a))
dataInterface (DataTypeInterface _ ctors) =
  let f (ConstructorDecl args) = args
  in f <$> ctors

-- commands take arguments (possibly including variables) and return a value
--
-- TODO: maybe rename this to `Command` if we do reuse it in instantiateAbility
data CommandDeclaration uid a = CommandDeclaration (Vector (ValTy uid a)) (ValTy uid a)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

data EffectInterface uid a = EffectInterface
  -- we universally quantify some number of type variables
  { _interfaceBinders :: Vector (a, Kind)
  -- a collection of commands
  , _commands :: Vector (CommandDeclaration uid a)
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

data InitiateAbility = OpenAbility | ClosedAbility
  deriving (Eq, Show, Ord, Typeable, Data, Generic)

-- "For each UID, instantiate it with these args"
data Ability uid a = Ability InitiateAbility (UIdMap uid (Vector (TyArg uid a)))
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

-- An adjustment is a mapping from effect inferface id to the types it's
-- applied to. IE a set of saturated interfaces.
newtype Adjustment uid a = Adjustment (UIdMap uid (Vector (TyArg uid a)))
  deriving (Monoid, Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Data, Generic)

-- Terms

data Value uid a b
  -- use (inferred)
  = Command Cid Row
  | ForeignFun Cid Row -- TODO: Is ForeignFun just a Command?

  -- construction (checked)
  | DataConstructor Cid Row (Vector (Tm uid a b))
  | Lambda (Scope Int (Tm uid a) b)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable, Data, Generic)

pattern CommandTm :: Cid -> Row -> Tm uid a b
pattern CommandTm uid row = Value (Command uid row)

pattern ForeignData :: Cid -> Value uid a b
pattern ForeignData uid = DataConstructor uid 0 []

pattern ForeignDataTm :: Cid -> Tm uid a b
pattern ForeignDataTm uid = Value (ForeignData uid)

pattern DataTm :: Cid -> Row -> Vector (Tm uid a b) -> Tm uid a b
pattern DataTm uid row vals = Value (DataConstructor uid row vals)

pattern ForeignFunTm :: Cid -> Row -> Tm uid a b
pattern ForeignFunTm uid row = Value (ForeignFun uid row)

data Continuation uid a b
  -- use (inferred)
  = Application (Spine uid a b)

  -- construction (checked)
  | Case uid (Vector (Scope Int (Tm uid a) b))
  | Handle
      (Adjustment uid a)
      (Peg uid a)
      (AdjustmentHandlers uid a b)
      (Scope () (Tm uid a) b)
  | Let (Polytype uid a) (Scope () (Tm uid a) b)

  -- Letrec
  --   :: Vector (Tm uid a b, PolytypeI)
  --   -> Scope Int (Tm uid a) b
  --   -> Continuation uid a b
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable, Data, Generic)

data Tm uid a b
  = Variable b
  | InstantiatePolyVar b (Vector (TyArg uid a))
  | Annotation (Value uid a b) (ValTy uid a)
  | Value (Value uid a b)
  | Cut (Continuation uid a b) (Tm uid a b)
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable, Data, Generic)

pattern V :: b -> Tm uid a b
pattern V name = Variable name

pattern CommandV :: Cid -> Row -> Tm uid a b
pattern CommandV uId row = Value (Command uId row)

pattern ConstructV :: Cid -> Row -> Vector (Tm uid a b) -> Tm uid a b
pattern ConstructV uId row args = Value (DataConstructor uId row args)

pattern LambdaV :: Scope Int (Tm uid a) b -> Tm uid a b
pattern LambdaV scope = Value (Lambda scope)


-- type? newtype?
type Spine uid a b = Vector (Tm uid a b)

-- Adjustment handlers are a mapping from effect interface id to the handlers
-- for each of that interface's constructors.
--
-- Encode each constructor argument (x_c) as a `Just Int` and the continuation
-- (z_c) as `Nothing`.
newtype AdjustmentHandlers uid a b = AdjustmentHandlers
  (UIdMap uid (Vector (Scope (Maybe Int) (Tm uid a) b)))
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable, Typeable, Data, Generic)

-- patterns
-- TODO: make these bidirectional

lam :: Eq b => Vector b -> Tm uid a b -> Value uid a b
lam vars body = Lambda (abstract (`elemIndex` vars) body)

case_
  :: (IsUid uid, Eq b)
  => uid
  -> Vector (Vector b, Tm uid a b)
  -> Continuation uid a b
case_ uid tms =
  let f (vars, tm) = abstract (`elemIndex` vars) tm
  in Case uid (f <$> tms)

handle
  :: forall uid a b.
     Eq b
  => Adjustment uid a
  -> Peg uid a
  -> UIdMap uid (Vector (Vector b, b, Tm uid a b))
  -> (b, Tm uid a b)
  -> Continuation uid a b
handle adj peg handlers (bodyVar, body) =
  let -- abstractor :: Vector b -> b -> b -> Maybe (Maybe Int)
      abstractor vars kVar var
        | var == kVar = Just Nothing
        | otherwise   = Just <$> elemIndex var vars
      handlers' = AdjustmentHandlers $
        (\(vars, kVar, rhs) -> abstract (abstractor vars kVar) rhs) <$$>
        handlers
      body' = abstract1 bodyVar body
  in Handle adj peg handlers' body'

let_ :: Eq b => b -> Polytype uid a -> Tm uid a b -> Value uid a b -> Tm uid a b
let_ name pty rhs body = Cut (Let pty (abstract1 name rhs)) (Value body)

-- letrec :: Eq b => Vector b -> Vector (Tm uid a b, Polytype uid a) -> Tm uid a b -> Tm uid a b
-- letrec names binderVals body =
--   Letrec binderVals (abstract (`elemIndex` names) body)

pattern VTy :: a -> ValTy uid a
pattern VTy name = VariableTy name

-- simple abilities

closedAbility :: IsUid uid => Ability uid a
closedAbility = Ability ClosedAbility mempty

emptyAbility :: IsUid uid => Ability uid a
emptyAbility = Ability OpenAbility mempty

extendAbility
  :: IsUid uid
  => Ability uid a
  -> Adjustment uid a
  -> Ability uid a
extendAbility (Ability initAb uidMap) (Adjustment adj)
  = Ability initAb (uidMap `uidMapUnion` adj)

type Executable1 f = f Cid Int
type Executable2 f = f Cid Int Int

type PolytypeI = Executable1 Polytype
type ValTyI    = Executable1 ValTy
type CompTyI   = Executable1 CompTy

type UseI                = Executable2 Tm
type ConstructionI       = Executable2 Tm
type AdjustmentHandlersI = Executable2 AdjustmentHandlers
type TmI                 = Executable2 Tm
type SpineI              = Spine Cid Int Int
type ValueI              = Executable2 Value

type AdjustmentI = Executable1 Adjustment
type AbilityI    = Executable1 Ability


-- Instance Hell:

instance IsUid uid => Unifiable (Ability uid) where
  unify (Ability init1 uids1) (Ability init2 uids2)
    = maybeIf (init1 == init2) (Ability init1 <$> unify uids1 uids2)

instance IsUid uid => Ord1 (Ability uid) where
  liftCompare cmp (Ability init1 entries1) (Ability init2 entries2) =
    compare init1 init2 <>
    liftCompare (liftCompare (liftCompare cmp))
      (toList entries1)
      (toList entries2)

instance IsUid uid => Unifiable (Peg uid) where
  unify (Peg ab1 val1) (Peg ab2 val2)
    = Peg <$> unify ab1 ab2 <*> unify val1 val2

instance IsUid uid => Ord1 (Peg uid) where
  liftCompare cmp (Peg ab1 val1) (Peg ab2 val2) =
    compare ab1 ab2 <>
    liftCompare cmp val1 val2

instance IsUid uid => Unifiable (CompTy uid) where
  unify (CompTy dom1 codom1) (CompTy dom2 codom2) = CompTy
    <$> unifyValTys dom1 dom2
    <*> unify codom1 codom2

unifyValTys
  :: (IsUid uid, Eq a)
  => Vector (ValTy uid a)
  -> Vector (ValTy uid a)
  -> Maybe (Vector (ValTy uid a))
unifyValTys vals1 vals2 = maybeIf
  (length vals1 == length vals2)
  (zipWithM unify vals1 vals2)

instance IsUid uid => Ord1 (CompTy uid) where
  liftCompare cmp (CompTy vt1 p1) (CompTy vt2 p2) =
    liftCompare (liftCompare cmp) vt1 vt2 <>
    liftCompare cmp p1 p2

instance IsUid uid => Unifiable (ValTy uid) where
  unify (DataTy uid1 args1) (DataTy uId2 args2) = maybeIf
    (uid1 == uId2)
    (DataTy uid1 <$> unifyTyArgs args1 args2)
  unify (SuspendedTy cty1) (SuspendedTy cty2) = SuspendedTy <$> unify cty1 cty2
  unify (VariableTy a) (VariableTy b) = maybeIf (a == b) (Just (VariableTy a))
  unify _ _ = Nothing

instance IsUid uid => Unifiable (TyArg uid) where
  unify (TyArgVal v1) (TyArgVal v2) = TyArgVal <$> unify v1 v2
  unify (TyArgAbility a1) (TyArgAbility a2) = TyArgAbility <$> unify a1 a2
  unify _ _ = Nothing

unifyTyArgs
  :: (IsUid uid, Eq a)
  => Vector (TyArg uid a)
  -> Vector (TyArg uid a)
  -> Maybe (Vector (TyArg uid a))
unifyTyArgs args1 args2 = maybeIf
  (length args1 == length args2)
  (zipWithM unify args1 args2)

instance IsUid uid => Ord1 (TyArg uid) where
  liftCompare cmp (TyArgVal valTy1) (TyArgVal valTy2)
    = liftCompare cmp valTy1 valTy2
  liftCompare _cmp (TyArgAbility ability1) (TyArgAbility ability2)
    = compare ability1 ability2
  liftCompare _ x y = compare (ordering x) (ordering y)
    where ordering = \case
            TyArgVal{}     -> 0 :: Int
            TyArgAbility{} -> 1

instance IsUid uid => Ord1 (ValTy uid) where
  liftCompare cmp l r = case (l, r) of
    (DataTy uid1 args1, DataTy uid2 args2) ->
      compare uid1 uid2 <> liftCompare (liftCompare cmp) args1 args2
    (SuspendedTy cty1, SuspendedTy cty2) -> liftCompare cmp cty1 cty2
    (VariableTy v1, VariableTy v2) -> cmp v1 v2
    (x, y) -> compare (ordering x) (ordering y)

          -- This section is rather arbitrary
    where ordering = \case
            DataTy{}      -> 0 :: Int
            SuspendedTy{} -> 1
            VariableTy{}  -> 2

instance Applicative (ValTy uid) where pure = VariableTy; (<*>) = ap

instance Monad (ValTy uid) where
  return = VariableTy

  DataTy uid args >>= f = DataTy uid ((`bindTyArg` f) <$> args)
  SuspendedTy (CompTy dom codom) >>= f = do
    let dom' = (>>= f) <$> dom
        codom' = bindPeg codom f
    SuspendedTy $ CompTy dom' codom'
  VariableTy a >>= f = f a

bindTyArg :: TyArg uid a -> (a -> ValTy uid b) -> TyArg uid b
bindTyArg (TyArgVal a) f = TyArgVal (a >>= f)
bindTyArg (TyArgAbility a) f = TyArgAbility a -- (bindAbility a f)

bindPeg :: Peg uid a -> (a -> ValTy uid b) -> Peg uid b
bindPeg (Peg ab val) f = Peg ab (val >>= f)

instance IsUid uid => Eq1 (ValTy uid) where
  liftEq eq (DataTy uid1 args1) (DataTy uid2 args2)
    = uid1 == uid2 && liftEq (liftEq eq) args1 args2
  liftEq eq (SuspendedTy cty1) (SuspendedTy cty2) = liftEq eq cty1 cty2
  liftEq eq (VariableTy v1) (VariableTy v2) = eq v1 v2
  liftEq _ _ _ = False

instance IsUid uid => Eq1 (CompTy uid) where
  liftEq eq (CompTy dom1 codom1) (CompTy dom2 codom2)
    = liftEq (liftEq eq) dom1 dom2 && liftEq eq codom1 codom2

instance IsUid uid => Eq1 (Peg uid) where
  liftEq eq (Peg ab1 val1) (Peg ab2 val2)
    = ab1 == ab2 && liftEq eq val1 val2

instance IsUid uid => Eq1 (TyArg uid) where
  liftEq eq (TyArgVal val1) (TyArgVal val2) = liftEq eq val1 val2
  liftEq _eq (TyArgAbility ab1) (TyArgAbility ab2) = ab1 == ab2
  liftEq _ _ _ = False

instance IsUid uid => Eq1 (Polytype uid) where
  liftEq eq (Polytype binders1 val1) (Polytype binders2 val2) =
    liftEq (==) binders1 binders2 && liftEq eq val1 val2

instance IsUid uid => Eq1 (Ability uid) where
  liftEq eq (Ability init1 entries1) (Ability init2 entries2) =
    init1 == init2 &&
    liftEq (liftEq (liftEq eq)) (toList entries1) (toList entries2)

instance (IsUid uid, Eq a) => Eq1 (AdjustmentHandlers uid a) where
  liftEq eq (AdjustmentHandlers handlers1) (AdjustmentHandlers handlers2) =
    liftEq (liftEq (liftEq eq)) (toList handlers1) (toList handlers2)

instance (IsUid uid, Ord a) => Ord1 (AdjustmentHandlers uid a) where
  liftCompare cmp (AdjustmentHandlers handlers1) (AdjustmentHandlers handlers2)
    = liftCompare (liftCompare (liftCompare cmp))
        (toList handlers1)
        (toList handlers2)

instance (IsUid uid, Eq e) => Eq1 (Value uid e) where
  liftEq _ (Command uid1 row1) (Command uid2 row2) =
    uid1 == uid2 && row1 == row2
  liftEq eq (DataConstructor uid1 row1 app1) (DataConstructor uid2 row2 app2) =
    uid1 == uid2 && row1 == row2 && liftEq (liftEq eq) app1 app2
  liftEq eq (Lambda body1) (Lambda body2) = liftEq eq body1 body2
  liftEq _ _ _ = False

instance (IsUid uid, Eq e) => Eq1 (Continuation uid e) where
  liftEq eq l r = case (l, r) of
    (Application spine1, Application spine2) ->
      liftEq (liftEq eq) spine1 spine2
    (Case uid1 rows1, Case uid2 rows2) ->
      uid1 == uid2 &&
      liftEq (liftEq eq) (toList rows1) (toList rows2)
    (Handle adj1 peg1 handlers1 body1, Handle adj2 peg2 handlers2 body2) ->
      adj1 == adj2 &&
      peg1 == peg2 &&
      liftEq eq handlers1 handlers2 &&
      liftEq eq body1 body2
    (Let pty1 body1, Let pty2 body2) ->
      pty1 == pty2 && liftEq eq body1 body2
    -- (Letrec binders1 body1, Letrec binders2 body2) ->
    --   liftEq bindersEq binders1 binders2 &&
    --   liftEq eq body1 body2
    _ -> False

instance (IsUid uid, Ord o) => Ord1 (Value uid o) where
  liftCompare cmp l r = case (l, r) of
    (Command uid1 row1, Command uid2 row2) ->
      compare uid1 uid2 <> compare row1 row2
    (DataConstructor uid1 row1 app1, DataConstructor uid2 row2 app2) ->
      compare uid1 uid2 <> compare row1 row2 <> liftCompare (liftCompare cmp) app1 app2
    (Lambda body1, Lambda body2) -> liftCompare cmp body1 body2
    (ForeignFun uid1 row1, ForeignFun uid2 row2) ->
      compare uid1 uid2 <> compare row1 row2
    (x, y) -> compare (ordering x) (ordering y)

    where ordering = \case
            Command{}            -> 0 :: Int
            DataConstructor{}    -> 1
            Lambda{}             -> 2
            ForeignFun{}         -> 3

instance (IsUid uid, Ord o) => Ord1 (Continuation uid o) where
  liftCompare cmp l r = case (l, r) of
    (Application spine1, Application spine2) ->
      liftCompare (liftCompare cmp) spine1 spine2
    (Case uid1 rows1, Case uid2 rows2) ->
      compare uid1 uid2 <>
      liftCompare (liftCompare cmp) (toList rows1) (toList rows2)
    (Handle adj1 peg1 handlers1 body1, Handle adj2 peg2 handlers2 body2) ->
      compare adj1 adj2 <>
      compare peg1 peg2 <>
      liftCompare cmp handlers1 handlers2 <>
      liftCompare cmp body1 body2
    (Let pty1 body1, Let pty2 body2) ->
      compare pty1 pty2 <> liftCompare cmp body1 body2
    -- (Letrec binders1 body1, Letrec binders2 body2) ->
    --   liftCompare bindersCmp binders1 binders2 <>
    --   liftCompare cmp body1 body2

    (x, y) -> compare (ordering x) (ordering y)

    where ordering = \case
            Application{}        -> 1 :: Int
            Case{}               -> 2
            Handle{}             -> 3
            Let{}                -> 4
            -- Letrec{}             -> 5

instance (IsUid uid, Eq e) => Eq1 (Tm uid e) where
  liftEq eq (Variable a) (Variable b) = eq a b
  liftEq eq (InstantiatePolyVar var1 args1) (InstantiatePolyVar var2 args2)
    = eq var1 var2 && liftEq (liftEq (==)) args1 args2
  liftEq eq (Annotation tm1 ty1) (Annotation tm2 ty2)
    = liftEq eq tm1 tm2 && liftEq (==) ty1 ty2
  liftEq eq (Value v1) (Value v2)
    = liftEq eq v1 v2
  liftEq eq (Cut cont1 val1) (Cut cont2 val2)
    = liftEq eq cont1 cont2 && liftEq eq val1 val2
  liftEq _ _ _ = False

instance (IsUid uid, Ord o) => Ord1 (Tm uid o) where
  liftCompare cmp (Variable a) (Variable b) = cmp a b
  liftCompare cmp (InstantiatePolyVar var1 args1) (InstantiatePolyVar var2 args2)
    = cmp var1 var2 <> liftCompare (liftCompare compare) args1 args2
  liftCompare cmp (Annotation tm1 ty1) (Annotation tm2 ty2)
    = liftCompare cmp tm1 tm2 <> liftCompare compare ty1 ty2
  liftCompare cmp (Value v1) (Value v2)
    = liftCompare cmp v1 v2
  liftCompare cmp (Cut cont1 val1) (Cut cont2 val2)
    = liftCompare cmp cont1 cont2 <> liftCompare cmp val1 val2
  liftCompare _ x y = compare (ordering x) (ordering y) where
    ordering = \case
      Variable{}           -> 0 :: Int
      InstantiatePolyVar{} -> 1
      Annotation{}         -> 2
      Value{}              -> 3
      Cut{}                -> 4

showSpace :: ShowS
showSpace = showString " "

instance Show uid => Show1 (ValTy uid) where
  liftShowsPrec s sl d valTy = showParen (d > 10) $ case valTy of
    DataTy uid tyArgs ->
        showString "DataTy "
      . shows uid
      . liftShowList s sl tyArgs
    SuspendedTy compTy ->
        showString "SuspendedTy "
      . liftShowsPrec s sl 11 compTy
    VariableTy a ->
        showString "VariableTy "
      . s 11 a

instance Show uid => Show1 (TyArg uid) where
  liftShowsPrec s sl d tyArg = showParen (d > 10) $ case tyArg of
    TyArgVal vTy ->
        showString "TyArgVal "
      . liftShowsPrec s sl 11 vTy
    TyArgAbility ab ->
        showString "TyArgAbility "
      . showsPrec 11 ab

instance Show uid => Show1 (CompTy uid) where
  liftShowsPrec s sl d (CompTy dom codom) = showParen (d > 10) $
      showString "CompTy "
    . liftShowList s sl dom
    . showSpace
    . liftShowsPrec s sl 11 codom

instance Show uid => Show1 (Peg uid) where
  liftShowsPrec s sl d (Peg ab val) = showParen (d > 10) $
      showString "Peg "
    . showsPrec 11 ab
    . showSpace
    . liftShowsPrec s sl 11 val

instance (Show uid, Show a) => Show1 (Value uid a) where
  liftShowsPrec s sl d val = showParen (d > 10) $ case val of
    Command uid row ->
        showString "Command "
      . shows uid
      . showSpace
      . shows row
    DataConstructor uid row tms ->
        showString "DataConstructor "
      . shows uid
      . showSpace
      . shows row
      . liftShowList s sl tms
    Lambda scope ->
        showString "Lambda "
      . liftShowsPrec s sl 11 scope
    ForeignFun uid row ->
        showString "ForeignFun "
      . shows uid
      . showSpace
      . shows row

instance (Show uid, Show a) => Show1 (Continuation uid a) where
  liftShowsPrec s sl d cont = showParen (d > 10) $ case cont of
    Application spine ->
        showString "Application "
      . liftShowList s sl spine
    Case uid branches ->
        showString "Case "
      . shows uid
      . showSpace
      . liftShowList s sl branches
    Handle adj peg handlers body ->
        showString "Handle "
      . showsPrec 11 adj
      . showSpace
      . showsPrec 11 peg
      . showSpace
      . liftShowsPrec s sl 11 handlers
      . showSpace
      . liftShowsPrec s sl 11 body
    Let pty body ->
        showString "Let"
      . showsPrec 11 pty
      . liftShowsPrec s sl 11 body
    -- Letrec _ _ -> showString "Letrec"

instance (Show uid, Show a) => Show1 (AdjustmentHandlers uid a) where
  liftShowsPrec s sl d (AdjustmentHandlers uidMap) = showParen (d > 10) $
      showString "AdjustmentHandlers "
    . liftShowList (liftShowsPrec s sl) (liftShowList s sl) (toList uidMap)

instance (Show uid, Show a) => Show1 (Tm uid a) where
  liftShowsPrec s sl d tm = showParen (d > 10) $ case tm of
    Variable b ->
        showString "Variable "
      . s 11 b
    InstantiatePolyVar b tys ->
        showString "InstantiatePolyVar "
      . s 11 b
      . showSpace
      . shows tys
    Annotation val valTy ->
        showString "Annotation "
      . liftShowsPrec s sl 11 val
      . showSpace
      . showsPrec 11 valTy
    Value val ->
        showString "Value "
      . liftShowsPrec s sl 11 val
    Cut cont tm' ->
        showString "Cut "
      . liftShowsPrec s sl 11 cont
      . showSpace
      . liftShowsPrec s sl 11 tm'

bindVal :: Value uid c a -> (a -> Tm uid c b) -> Value uid c b
bindVal (Command uid row) _ = Command uid row
bindVal (DataConstructor uid row tms) f =
  DataConstructor uid row ((>>= f) <$> tms)
bindVal (Lambda body) f = Lambda (body >>>= f)
bindVal (ForeignFun uid row) _ = ForeignFun uid row

bindContinuation :: Continuation uid c a -> (a -> Tm uid c b) -> Continuation uid c b
bindContinuation (Application spine) f = Application ((>>= f) <$> spine)
bindContinuation (Case uid branches) f = Case uid ((>>>= f) <$> branches)
bindContinuation (Handle adj peg (AdjustmentHandlers handlers) rhs) f = Handle
  adj
  peg
  (AdjustmentHandlers ((>>>= f) <$$> handlers))
  (rhs >>>= f)
bindContinuation (Let poly rhs) f = Let poly (rhs >>>= f)

instance Applicative (Tm uid a) where pure = Variable; (<*>) = ap
instance Monad (Tm uid a) where
  return = Variable

  -- (>>=) :: Tm uid c a -> (a -> Tm uid c b) -> Tm uid c b
  Variable a >>= f = f a
  InstantiatePolyVar a _ >>= f = f a
  Annotation val ty >>= f = Annotation (bindVal val f) ty
  Value v >>= f = Value (bindVal v f)
  Cut neg pos >>= f = Cut (bindContinuation neg f) (pos >>= f)

-- Lens Hell:

makeLenses ''EffectInterface
