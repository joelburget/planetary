{-# language LambdaCase #-}
{-# language GADTs #-}
{-# language KindSignatures #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language DataKinds #-}
{-# language TupleSections #-}
{-# language PatternSynonyms #-}
{-# language Rank2Types #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language DeriveFunctor #-}
{-# language DeriveFoldable #-}
{-# language DeriveTraversable #-}
module Interplanetary.Syntax where

import Bound
import Control.Monad (ap)
import Data.Functor.Classes
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap as IntMap
import Data.List (elemIndex)
import Data.Monoid ((<>))

import Interplanetary.Util

-- TODO:
-- * Right now we use simple equality to check types but should implement
--   unification
-- * Be more granular about the capabilities each function needs instead of
--   hardcoding its monad.
-- * What libraries should we be using?
--   - bound
--   - unification-fd
-- * Error messaging is pitiful
--   - show some sort of helpful info
--   - our errors are essentially meaningless
-- * Should type and effect variables share a namespace?

type Uid = Int
type Row = Int

-- Types

data ValTy a
  = DataTy Uid (Vector (TyArg a))
  | SuspendedTy (CompTy a)
  | VariableTy a
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

data CompTy a = CompTy
  { compDomain :: Vector (ValTy a)
  , compCodomain :: Peg a
  } deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

data Peg a = Peg
  { pegAbility :: Ability a
  , pegVal :: ValTy a
  } deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

data TyArg a
  = TyArgVal (ValTy a)
  | TyArgAbility (Ability a)
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

data Kind = ValTy | EffTy
  deriving (Show, Eq, Ord)

data Polytype a = Polytype
  -- Universally quantify over a bunch of variables
  { polyBinders :: Vector Kind
  -- resulting in a value type
  , polyVal :: Scope Int ValTy a
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

polytype :: Eq a => Vector (a, Kind) -> ValTy a -> Polytype a
polytype binders body =
  let (names, kinds) = unzip binders
  in Polytype kinds (abstract (`elemIndex` names) body)

instance Show1 ValTy where
instance Ord1 ValTy where
instance Applicative ValTy where
instance Monad ValTy where

data DataConstructor a = DataConstructor (Vector (ValTy a))
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- A collection of data constructor signatures (which can refer to bound type /
-- effect variables).
data DataTypeInterface a = DataTypeInterface
  -- { dataTypeUid :: Uid
  -- we universally quantify over some number of type variables
  { dataBinders :: Vector (a, Kind)
  -- a collection of constructors taking some arguments
  , constructors :: Vector (DataConstructor a)
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

-- commands take arguments (possibly including variables) and return a value
data CommandDeclaration a = CommandDeclaration (Vector (ValTy a)) (ValTy a)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data EffectInterface a = EffectInterface
  -- we universally quantify some number of type variables
  { interfaceBinders :: Vector (a, Kind)
  -- a collection of commands
  , commands :: Vector (CommandDeclaration a)
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

data InitiateAbility a = OpenAbility a | ClosedAbility
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

data Ability a = Ability (InitiateAbility a) (IntMap (Vector (TyArg a)))
  deriving (Eq, Show, Ord, Functor, Foldable, Traversable)

-- An adjustment is a mapping from effect inferface id to the types it's
-- applied to. IE a set of saturated interfaces.
newtype Adjustment a = Adjustment (IntMap {- Uid -> -} (Vector (TyArg a)))
  deriving (Monoid, Show, Eq, Ord, Functor, Foldable, Traversable)

-- TODO: move all the tables into here
data TypingEnv a = TypingEnv (Stack (Either (ValTy a) (Polytype a)))

type DataTypeTable a = IntMap (Vector (Vector (ValTy a)))
type VarTyTable a = Stack (Either (ValTy a) (Polytype a)) -- IntMap ValTy
type InterfaceTable a = IntMap (EffectInterface a)

-- Terms

data Tm :: * -> * -> * where
  -- inferred
  Variable            :: b                          -> Tm a b
  InstantiatePolyVar  :: b      -> Vector (TyArg a) -> Tm a b
  Command             :: Uid    -> Row              -> Tm a b
  OperatorApplication :: Tm a b -> Spine a b        -> Tm a b
  Annotation          :: Tm a b -> ValTy a          -> Tm a b

  -- checked
  ConstructUse :: Tm a b                                -> Tm a b
  Construct    :: Uid  -> Row -> Vector (Tm a b)        -> Tm a b
  Lambda       :: Scope Int (Tm a) b                    -> Tm a b
  Case         :: Tm a b -> Vector (Scope Int (Tm a) b) -> Tm a b
  Handle
    :: Adjustment a
    -> Tm a b
    -> AdjustmentHandlers a b
    -> Scope () (Tm a) b
    -> Tm a b
  Let
    :: Polytype a
    -> Tm a b
    -> Scope () (Tm a) b
    -> Tm a b
  Letrec
    :: Vector (Tm a b, Polytype a)
    -> Scope Int (Tm a) b
    -> Tm a b

-- type? newtype?
type Spine a b = Vector (Tm a b)

-- Adjustment handlers are a mapping from effect interface id to the handlers
-- for each of that interface's constructors.
newtype AdjustmentHandlers a b = AdjustmentHandlers
  (IntMap {- Uid -> -} (Vector (Scope Int (Tm a) b)))
  deriving (Eq, Ord, Show, Functor, Foldable, Traversable)

-- patterns

lam :: Eq b => Vector b -> Tm a b -> Tm a b
lam vars body = Lambda (abstract (`elemIndex` vars) body)

let_ :: Eq b => b -> Polytype a -> Tm a b -> Tm a b -> Tm a b
let_ name ty rhs body = Let ty rhs (abstract1 name body)

letrec :: Eq b => Vector b -> Vector (Tm a b, Polytype a) -> Tm a b -> Tm a b
letrec names binderVals body =
  Letrec binderVals (abstract (`elemIndex` names) body)

pattern V :: b -> Tm a b
pattern V name = Variable name

pattern VTy :: a -> ValTy a
pattern VTy name = VariableTy name

-- simple abilities

closedAbility :: Ability a
closedAbility = Ability ClosedAbility IntMap.empty

-- TODO: This `OpenAbility e` makes me uncomfortable
emptyAbility :: Ability String
emptyAbility = Ability (OpenAbility "e") IntMap.empty


-- Instance Hell:

deriving instance (Eq a, Eq b) => Eq (Tm a b)
deriving instance (Ord a, Ord b) => Ord (Tm a b)
deriving instance (Show a, Show b) => Show (Tm a b)
deriving instance Functor (Tm a)
deriving instance Foldable (Tm a)
deriving instance Traversable (Tm a)
instance Applicative (Tm a) where pure = Variable; (<*>) = ap

instance Eq1 ValTy where
  liftEq eq (DataTy uid1 args1) (DataTy uid2 args2)
    = uid1 == uid2 && liftEq (liftEq eq) args1 args2
  liftEq eq (SuspendedTy cty1) (SuspendedTy cty2) = liftEq eq cty1 cty2
  liftEq eq (VariableTy v1) (VariableTy v2) = eq v1 v2
  liftEq _ _ _ = False

instance Eq1 CompTy where
  liftEq eq (CompTy dom1 codom1) (CompTy dom2 codom2)
    = liftEq (liftEq eq) dom1 dom2 && liftEq eq codom1 codom2

instance Eq1 Peg where
  liftEq eq (Peg ab1 val1) (Peg ab2 val2)
    = liftEq eq ab1 ab2 && liftEq eq val1 val2

instance Eq1 TyArg where
  liftEq eq (TyArgVal val1) (TyArgVal val2) = liftEq eq val1 val2
  liftEq eq (TyArgAbility ab1) (TyArgAbility ab2) = liftEq eq ab1 ab2
  liftEq _ _ _ = False

instance Eq1 Polytype where
  liftEq eq (Polytype binders1 val1) (Polytype binders2 val2) =
    liftEq (==) binders1 binders2 && liftEq eq val1 val2

instance Eq1 Ability
instance Eq1 InitiateAbility
instance Eq a => Eq1 (AdjustmentHandlers a)
instance Ord a => Ord1 (AdjustmentHandlers a)

instance Eq e => Eq1 (Tm e) where
  liftEq eq l r = case (l, r) of
    (Variable a, Variable b) -> eq a b
    (InstantiatePolyVar var1 args1, InstantiatePolyVar var2 args2) ->
      liftEq (==) args1 args2 && eq var1 var2
    (Command uid1 row1, Command uid2 row2) -> uid1 == uid2 && row1 == row2
    (OperatorApplication op1 spine1, OperatorApplication op2 spine2) ->
      liftEq eq op1 op2 && liftEq (liftEq eq) spine1 spine2
    (Annotation tm1 ty1, Annotation tm2 ty2) ->
      liftEq eq tm1 tm2 && ty1 == ty2
    (ConstructUse tm1, ConstructUse tm2) -> liftEq eq tm1 tm2
    (Construct uid1 row1 app1, Construct uid2 row2 app2) ->
      uid1 == uid2 && row1 == row2 && liftEq (liftEq eq) app1 app2
    (Lambda body1, Lambda body2) -> liftEq eq body1 body2
    (Case tm1 rows1, Case tm2 rows2) ->
      liftEq eq tm1 tm2 && liftEq (liftEq eq) rows1 rows2
    (Handle adj1 rhs1 handlers1 body1, Handle adj2 rhs2 handlers2 body2) ->
      adj1 == adj2 &&
      liftEq eq rhs1 rhs2 &&
      liftEq eq handlers1 handlers2 &&
      liftEq eq body1 body2
    (Let pty1 tm1 body1, Let pty2 tm2 body2) ->
      pty1 == pty2 && liftEq eq tm1 tm2 && liftEq eq body1 body2
    (Letrec binders1 body1, Letrec binders2 body2) ->
      liftEq bindersEq binders1 binders2 &&
      liftEq eq body1 body2
    _ -> False

          -- bindersEq :: (Tm t a, Polytype t) -> (Tm t b, Polytype t) -> Bool
          -- bindersEq l r = eq' *** (==)
    where bindersEq (tm1, pty1) (tm2, pty2) = liftEq eq tm1 tm2 && pty1 == pty2

instance Ord o => Ord1 (Tm o) where
  liftCompare cmp l r = case (l, r) of
    (Variable a, Variable b) -> cmp a b
    (InstantiatePolyVar var1 args1, InstantiatePolyVar var2 args2) ->
      liftCompare compare args1 args2 <> cmp var1 var2
    (Command uid1 row1, Command uid2 row2) ->
      compare uid1 uid2 <> compare row1 row2
    (OperatorApplication op1 spine1, OperatorApplication op2 spine2) ->
      (liftCompare cmp) op1 op2 <> liftCompare (liftCompare cmp) spine1 spine2
    (Annotation tm1 ty1, Annotation tm2 ty2) ->
      (liftCompare cmp) tm1 tm2 <> compare ty1 ty2
    (ConstructUse tm1, ConstructUse tm2) -> (liftCompare cmp) tm1 tm2
    (Construct uid1 row1 app1, Construct uid2 row2 app2) ->
      compare uid1 uid2 <> compare row1 row2 <> liftCompare (liftCompare cmp) app1 app2
    (Lambda body1, Lambda body2) -> (liftCompare cmp) body1 body2
    (Case tm1 rows1, Case tm2 rows2) ->
      (liftCompare cmp) tm1 tm2 <> liftCompare (liftCompare cmp) rows1 rows2
    (Handle adj1 rhs1 handlers1 body1, Handle adj2 rhs2 handlers2 body2) ->
      compare adj1 adj2 <>
      (liftCompare cmp) rhs1 rhs2 <>
      liftCompare cmp handlers1 handlers2 <>
      (liftCompare cmp) body1 body2
    (Let pty1 tm1 body1, Let pty2 tm2 body2) ->
      compare pty1 pty2 <> (liftCompare cmp) tm1 tm2 <> (liftCompare cmp) body1 body2
    (Letrec binders1 body1, Letrec binders2 body2) ->
      liftCompare bindersCmp binders1 binders2 <>
      liftCompare cmp body1 body2

    (x, y) -> compare (ordering x) (ordering y)

          -- bindersCmp :: forall a b t. Ord t => (Tm t a, Polytype t) -> (Tm t b, Polytype t) -> Ordering
          -- bindersCmp l r = cmp' *** compare
    where bindersCmp (tm1, pty1) (tm2, pty2) =
            liftCompare cmp tm1 tm2 <> compare pty1 pty2

          -- This section is rather arbitrary
          ordering = \case
            Variable{}            -> (0 :: Int)
            InstantiatePolyVar{}  -> 1
            Command{}             -> 2
            OperatorApplication{} -> 3
            Annotation{}          -> 4
            ConstructUse{}        -> 5
            Construct{}           -> 6
            Lambda{}              -> 7
            Case{}                -> 8
            Handle{}              -> 9
            Let{}                 -> 10
            Letrec{}              -> 11

instance Show a => Show1 (Tm a) where
  liftShowsPrec s sl d = \case
    -- TODO, obviously
    Variable b -> showParen (d > 10) $ showString "Variable " . s 11 b
    InstantiatePolyVar b tys -> showParen (d > 10) $
      showString "InstantiatePolyVar " . s 11 b . showString " " . shows tys
    Command uid row ->
      showString "Command " . shows uid . showString " " . shows row
    OperatorApplication tm spine ->
      showString "OperatorApplication " .
      liftShowsPrec s sl d tm .
      liftShowList s sl spine
    Annotation _ _ -> showString "Annotation"
    ConstructUse _ -> showString "ConstructUse"
    Construct _ _ _ -> showString "Construct"
    Lambda scope -> liftShowsPrec s sl d scope
    Case _ _ -> showString "Case"
    Handle _ _ _ _ -> showString "Handle"
    Let _ _ _ -> showString "Let"
    Letrec _ _ -> showString "Letrec"
    -- TODO

instance Monad (Tm a) where
  return = Variable

  Variable a >>= f = f a
  InstantiatePolyVar a _ >>= f = f a
  Command uid row >>= _ = Command uid row
  OperatorApplication tm spine >>= f
    = OperatorApplication (tm >>= f) ((>>= f) <$> spine)
  Annotation tm ty >>= f = Annotation (tm >>= f) ty

  ConstructUse tm >>= f = ConstructUse (tm >>= f)
  Construct uid row tms >>= f = Construct uid row ((>>= f) <$> tms)
  Lambda body >>= f = Lambda (body >>>= f)
  Case tm branches >>= f = Case (tm >>= f) ((>>>= f) <$> branches)
  Handle adj body (AdjustmentHandlers handlers) rhs >>= f = Handle
    adj
    (body >>= f)
    (AdjustmentHandlers ((fmap.fmap) (>>>= f) handlers))
    (rhs >>>= f)
  Let poly body rhs >>= f = Let poly (body >>= f) (rhs >>>= f)
  Letrec bindings rhs >>= f =
    let g (tm, poly) = (tm >>= f, poly)
    in Letrec (g <$> bindings) (rhs >>>= f)
