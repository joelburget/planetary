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
{-# language NamedFieldPuns #-}
{-# language PatternSynonyms #-}
{-# language Rank2Types #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language TupleSections #-}
{-# language TypeFamilies #-}
{-# language ViewPatterns #-}
-- I don't want to annotate all the pattern synonyms
{-# options_ghc -fno-warn-missing-pattern-synonym-signatures #-}
module Planetary.Core.Syntax (module Planetary.Core.Syntax) where

import Bound
import Control.Lens
import Control.Lens.TH (makeLenses)
import Control.Monad (ap)
import Data.Data
import Data.Foldable (toList)
import Data.Functor.Classes
import Data.List (find)
import Data.Monoid ((<>))
import Data.Text (Text)
import Data.Traversable (fmapDefault, foldMapDefault)
import qualified Data.Vector as V
import GHC.Generics
import Network.IPLD hiding (Value, Row)
import qualified Network.IPLD as IPLD

import Planetary.Core.Orphans ()
import Planetary.Core.UIdMap
import Planetary.Util

-- TODO:
-- * Right now we use an extremely simple form of unification -- switch to
--   logict or something
-- * Be more granular about the capabilities each function needs instead of
--   hardcoding its monad.
-- * Error messaging is pitiful
--   - show some sort of helpful info
--   - our errors are essentially meaningless
-- * Should type and effect variables share a namespace?

type Row = Int

-- Types

data InitiateAbility = OpenAbility | ClosedAbility
  deriving (Eq, Show, Ord, Typeable, Generic)

data TyTag
  = VALTY
  | COMPTY
  | PEG
  | TYARG
  | ABILITY

data Kind = ValTyK | EffTyK
  deriving (Show, Eq, Ord, Typeable, Generic)

data Ty (tag :: TyTag) uid a where
  DataTy :: uid -> Vector (TyArg uid a) -> Ty 'VALTY uid a
  SuspendedTy :: CompTy uid a -> Ty 'VALTY uid a
  VariableTy :: a -> Ty 'VALTY uid a

  -- CompTy
  CompTy :: Vector (ValTy uid a) -> Peg uid a -> Ty 'COMPTY uid a
  -- { compDomain :: , compCodomain ::

  -- Peg
  Peg :: Ability uid a -> ValTy uid a -> Ty 'PEG uid a

  -- TyArg
  TyArgVal :: ValTy uid a -> Ty 'TYARG uid a
  TyArgAbility :: Ability uid a -> Ty 'TYARG uid a

  -- Ability
  -- "For each UID, instantiate it with these args"
  Ability :: InitiateAbility -> UIdMap uid (Vector (TyArg uid a)) -> Ty 'ABILITY uid a

type ValTy   = Ty 'VALTY
type CompTy  = Ty 'COMPTY
type Peg     = Ty 'PEG
type TyArg   = Ty 'TYARG
type Ability = Ty 'ABILITY

deriving instance (Show uid, Show a) => Show (Ty tag uid a)
deriving instance (Eq uid, Eq a) => Eq (Ty tag uid a)
deriving instance Typeable (Ty tag uid a)
deriving instance Functor (Ty tag uid)
deriving instance Foldable (Ty tag uid)
deriving instance Traversable (Ty tag uid)

instance (IsUid uid, Ord a) => Ord (Ty tag uid a) where
  compare = liftCompare compare

data Polytype uid a = Polytype
  -- Universally quantify over a bunch of variables
  { polyBinders :: Vector (a, Kind)
  -- resulting in a value type
  , polyVal :: Scope Int (ValTy uid) a
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic)

data ConstructorDecl uid a = ConstructorDecl
  { _constructorName   :: Text
  , _constructorArgs   :: Vector (ValTy uid a)
  , _constructorResult :: Vector (TyArg uid a)
  }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic)

-- A collection of data constructor signatures (which can refer to bound type /
-- effect variables).
data DataTypeInterface uid a = DataTypeInterface
  -- we universally quantify over some number of type variables
  { _dataBinders :: Vector (Text, Kind)
  -- a collection of constructors taking some arguments
  , _constructors :: Vector (ConstructorDecl uid a)
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic)

emptyDataTypeInterface :: DataTypeInterface uid a
emptyDataTypeInterface = DataTypeInterface [] []

-- commands take arguments (possibly including variables) and return a value
--
-- TODO: maybe rename this to `Command` if we do reuse it in instantiateAbility
data CommandDeclaration uid a = CommandDeclaration (Vector (ValTy uid a)) (ValTy uid a)
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic)

data EffectInterface uid a = EffectInterface
  -- we universally quantify some number of type variables
  { _interfaceBinders :: Vector (a, Kind)
  -- a collection of commands
  , _commands :: Vector (CommandDeclaration uid a)
  } deriving (Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic)

-- An adjustment is a mapping from effect inferface id to the types it's
-- applied to. IE a set of saturated interfaces.
newtype Adjustment uid a = Adjustment (UIdMap uid (Vector (TyArg uid a)))
  deriving (Monoid, Show, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic)

-- Terms

data TmTag
  = VALUE
  | CONTINUATION
  | TM
  | ADJUSTMENT_HANDLERS

data Tm (tag :: TmTag) uid a b where
  -- Term:
  -- use (inferred)
  Command :: uid -> Row -> Tm 'VALUE uid a b

  -- construction (checked)
  DataConstructor :: uid -> Row -> Vector (Tm 'TM uid a b) -> Tm 'VALUE uid a b
  ForeignValue :: uid -> Vector (ValTy uid a) -> uid -> Tm 'VALUE uid a b
  Lambda :: Vector Text -> Scope Int (Tm 'TM uid a) b -> Tm 'VALUE uid a b

  -- Continuation:
  -- use (inferred)
  Application :: Spine uid a b -> Tm 'CONTINUATION uid a b

  -- construction (checked)
  Case
    :: uid
    -> Vector (Vector Text, Scope Int (Tm 'TM uid a) b)
    -> Tm 'CONTINUATION uid a b
  Handle
    :: Adjustment uid a
    -> Peg uid a
    -> Tm 'ADJUSTMENT_HANDLERS uid a b
    -> Scope () (Tm 'TM uid a) b
    -> Tm 'CONTINUATION uid a b
  Let
    :: Polytype uid a
    -> Text
    -> Scope () (Tm 'TM uid a) b
    -> Tm 'CONTINUATION uid a b

  -- Term
  Variable :: b -> Tm 'TM uid a b
  InstantiatePolyVar :: b -> Vector (TyArg uid a) -> Tm 'TM uid a b
  Annotation :: Tm 'VALUE uid a b -> ValTy uid a -> Tm 'TM uid a b
  Value :: Tm 'VALUE uid a b -> Tm 'TM uid a b
  Cut :: Tm 'CONTINUATION uid a b -> Tm 'TM uid a b  -> Tm 'TM uid a b
  Letrec
    -- invariant: each value is a lambda
    :: Vector (Polytype uid a, Tm 'VALUE uid a b)
    -> Scope Int (Tm 'TM uid a) b
    -> Tm 'TM uid a b

  -- Other
  -- Adjustment handlers are a mapping from effect interface id to the handlers
  -- for each of that interface's constructors.
  --
  -- Encode each constructor argument (x_c) as a `Just Int` and the
  -- continuation (z_c) as `Nothing`.
  AdjustmentHandlers
    :: UIdMap uid (Vector (Scope (Maybe Int) (Tm 'TM uid a) b))
    -> Tm 'ADJUSTMENT_HANDLERS uid a b

-- type? newtype?
type Spine uid a b = Vector (Tm 'TM uid a b)

data Decl uid a b
  = DataDecl_      (DataDecl uid a)
  | InterfaceDecl_ (InterfaceDecl uid a)
  | TermDecl_      (TermDecl uid a b)
  deriving (Eq, Ord, Show, Typeable, Generic)

data DataDecl uid a = DataDecl Text (DataTypeInterface uid a)
  deriving (Eq, Ord, Show, Typeable, Generic)

data InterfaceDecl uid a = InterfaceDecl Text (EffectInterface uid a)
  deriving (Eq, Ord, Show, Typeable, Generic)

data TermDecl uid a b = TermDecl
  Text            -- ^ the term's name
  (Tm 'TM uid a b) -- ^ body
  deriving (Typeable, Generic)

deriving instance (IsUid uid, Eq a, Eq b) => Eq (TermDecl uid a b)
deriving instance (IsUid uid, Ord a, Ord b) => Ord (TermDecl uid a b)
deriving instance (Show uid, Show a, Show b) => Show (TermDecl uid a b)

type DeclS          = Decl          Text Text Text
type DataDeclS      = DataDecl      Text Text
type InterfaceDeclS = InterfaceDecl Text Text
type TermDeclS      = TermDecl      Text Text Text

data ResolvedDecls = ResolvedDecls
  { _datatypes  :: UIdMap Cid DataTypeInterfaceI
  , _interfaces :: UIdMap Cid EffectInterfaceI
  , _globalCids :: [(Text, Cid)]
  , _terms      :: [Executable2 TermDecl]
  } deriving Show

-- TODO: make traversals
-- namedData :: Text -> Traversal' ResolvedDecls DataTypeInterfaceI

namedData :: Text -> ResolvedDecls -> Maybe (Cid, DataTypeInterfaceI)
namedData name decls = do
  (_, cid) <- find ((== name) . fst) (_globalCids decls)
  (cid,) <$> _datatypes decls ^? ix cid

namedInterface :: Text -> ResolvedDecls -> Maybe (Cid, EffectInterfaceI)
namedInterface name decls = do
  (_, cid) <- find ((== name) . fst) (_globalCids decls)
  (cid,) <$> _interfaces decls ^? ix cid

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

-- executable

type Executable1 f = f Cid Int
type Executable2 f = f Cid Int Int

type AbilityI            = Executable1 Ability
type AdjustmentI         = Executable1 Adjustment
type CommandDeclarationI = Executable1 CommandDeclaration
type CompTyI             = Executable1 CompTy
type PolytypeI           = Executable1 Polytype
type ValTyI              = Executable1 ValTy
type TyArgI              = Executable1 TyArg
type DataTypeInterfaceI  = Executable1 DataTypeInterface
type EffectInterfaceI    = Executable1 EffectInterface
type ConstructorDeclI    = Executable1 ConstructorDecl
type PegI                = Executable1 Peg

type TmI                 = Executable2 (Tm 'TM)
type ValueI              = Executable2 (Tm 'VALUE)
type ContinuationI       = Executable2 (Tm 'CONTINUATION)
type AdjustmentHandlersI = Executable2 (Tm 'ADJUSTMENT_HANDLERS)
type SpineI              = Spine Cid Int Int
type UseI                = TmI
type ConstructionI       = TmI

-- raw

type Raw1 f = f Text Text
type Raw2 f = f Text Text Text

type Ability'            = Raw1 Ability
type Adjustment'         = Raw1 Adjustment
type CommandDeclaration' = Raw1 CommandDeclaration
type CompTy'             = Raw1 CompTy
type ConstructorDecl'    = Raw1 ConstructorDecl
type Peg'                = Raw1 Peg
type Polytype'           = Raw1 Polytype
type TyArg'              = Raw1 TyArg
type ValTy'              = Raw1 ValTy

type Tm'                 = Raw2 (Tm 'TM)
type Value'              = Raw2 (Tm 'VALUE)
type Continuation'       = Raw2 (Tm 'CONTINUATION)
type AdjustmentHandlers' = Raw2 (Tm 'ADJUSTMENT_HANDLERS)
type Spine'              = Spine Text Text Text
type Construction        = Tm'
type Use                 = Tm'
type Cont'               = Continuation'

-- utils:

-- | abstract 0 variables
abstract0 :: Monad f => f a -> Scope b f a
abstract0 = abstract
  (error "abstract0 being used to instantiate > 0 variables")

closeVar :: Eq a => (a, b) -> Tm 'TM uid c a -> Maybe (Tm 'TM uid c b)
closeVar (a, b) = instantiate1 (Variable b) <$$> closed . abstract1 a

-- closeVars :: (Eq a, Hashable a) => [(a, b)] -> Tm uid c a -> Maybe (Tm uid c b)
-- closeVars vars =
--   let mapping = HashMap.fromList vars
--       abstractor k = HashMap.lookup k mapping
--   in instantiate Variable <$$> closed . abstract abstractor


-- Instance Hell:

-- IsIpld

pattern Vx :: [a] -> V.Vector a
pattern Vx lst <- (V.toList -> lst) where
  Vx lst = V.fromList lst

pattern T1 :: IsIpld a => Text -> a -> IPLD.Value
pattern T1 tag a <- (DagArray (Vx [fromIpld -> Just tag, fromIpld -> Just a])) where
  T1 tag a = DagArray (Vx [toIpld tag, toIpld a])

pattern T2 :: (IsIpld a, IsIpld b) => Text -> a -> b -> IPLD.Value
pattern T2 tag a b <- (DagArray (Vx [fromIpld -> Just tag, fromIpld -> Just a, fromIpld -> Just b])) where
  T2 tag a b = DagArray (Vx [toIpld tag, toIpld a, toIpld b])

pattern T3 :: (IsIpld a, IsIpld b, IsIpld c) => Text -> a -> b -> c -> IPLD.Value
pattern T3 tag a b c <- (DagArray (Vx [fromIpld -> Just tag, fromIpld -> Just a, fromIpld -> Just b, fromIpld -> Just c])) where
  T3 tag a b c = DagArray (Vx [toIpld tag, toIpld a, toIpld b, toIpld c])

pattern T4 :: (IsIpld a, IsIpld b, IsIpld c, IsIpld d) => Text -> a -> b -> c -> d -> IPLD.Value
pattern T4 tag a b c d <- (DagArray (Vx [fromIpld -> Just tag, fromIpld -> Just a, fromIpld -> Just b, fromIpld -> Just c, fromIpld -> Just d])) where
  T4 tag a b c d = DagArray (Vx [toIpld tag, toIpld a, toIpld b, toIpld c, toIpld d])

pattern DataTyIpld uid args     = T2 "DataTy" uid args
pattern SuspendedTyIpld cty     = T1 "SuspendedTy" cty
pattern VariableTyIpld var      = T1 "VariableTy" var
pattern CompTyIpld dom codom    = T2 "CompTy" dom codom
pattern PegIpld ab ty           = T2 "Peg" ab ty
pattern TyArgValIpld ty         = T1 "TyArgVal" ty
pattern TyArgAbilityIpld ab     = T1 "TyArgAbility" ab
pattern AbilityIpld init uidmap = T2 "Ability" init uidmap

instance (IsUid uid, IsIpld a) => IsIpld (Ty 'VALTY uid a) where
  toIpld = \case
    DataTy uid args -> DataTyIpld uid args
    SuspendedTy cty -> SuspendedTyIpld cty
    VariableTy var  -> VariableTyIpld var

  fromIpld = \case
    DataTyIpld uid args -> Just $ DataTy uid args
    SuspendedTyIpld cty -> Just $ SuspendedTy cty
    VariableTyIpld var  -> Just $ SuspendedTy var
    _ -> Nothing

instance (IsUid uid, IsIpld a) => IsIpld (Ty 'COMPTY uid a) where
  toIpld (CompTy dom codom) = CompTyIpld dom codom
  fromIpld = \case
    CompTyIpld dom codom -> Just $ CompTy dom codom
    _ -> Nothing

instance (IsUid uid, IsIpld a) => IsIpld (Ty 'PEG uid a) where
  toIpld (Peg ab ty) = PegIpld ab ty
  fromIpld = \case
    PegIpld ab ty -> Just $ Peg ab ty
    _ -> Nothing

instance (IsUid uid, IsIpld a) => IsIpld (Ty 'TYARG uid a) where
  toIpld = \case
    TyArgVal ty -> TyArgValIpld ty
    TyArgAbility ab -> TyArgAbilityIpld ab
  fromIpld = \case
    TyArgValIpld ty -> Just $ TyArgVal ty
    TyArgAbilityIpld ab -> Just $ TyArgAbility ab
    _ -> Nothing

instance (IsUid uid, IsIpld a) => IsIpld (Ty 'ABILITY uid a) where
  toIpld (Ability i uidmap) = AbilityIpld i uidmap
  fromIpld = \case
    AbilityIpld i uidmap -> Just $ Ability i uidmap
    _ -> Nothing

pattern CommandIpld uid row             = T2 "Command" uid row
pattern DataConstructorIpld uid row tms = T3 "DataConstructor" uid row tms
pattern ForeignValueIpld uid1 tys uid2  = T3 "ForeignValue" uid1 tys uid2
pattern LambdaIpld body                 = T1 "Lambda" body
pattern ApplicationIpld spine           = T1 "Application" spine
pattern CaseIpld uid branches           = T2 "Case" uid branches
pattern HandleIpld adj peg handlers valHandler
  = T4 "Handle" adj peg handlers valHandler
pattern LetIpld pty scope               = T2 "LetIpld" pty scope
pattern VariableIpld b                  = T1 "Variable" b
pattern InstantiatePolyVarIpld b args   = T2 "InstantiatePolyVar" b args
pattern AnnotationIpld tm ty            = T2 "Annotation" tm ty
pattern ValueIpld tm                    = T1 "Value" tm
pattern CutIpld cont scrutinee          = T2 "Cut" cont scrutinee
pattern LetrecIpld defns body           = T2 "Letrec" defns body
pattern AdjustmentHandlersIpld uidmap   = T1 "AdjustmentHandlers" uidmap

instance (IsUid uid, IsIpld a, IsIpld b) => IsIpld (Tm 'VALUE uid a b) where
  toIpld = \case
    Command uid row             -> CommandIpld uid row
    DataConstructor uid row tms -> DataConstructorIpld uid row tms
    ForeignValue uid1 tys uid2  -> ForeignValueIpld uid1 tys uid2
    Lambda _names body          -> LambdaIpld body

  fromIpld = \case
    CommandIpld uid row             -> Just $ Command uid row
    DataConstructorIpld uid row tms -> Just $ DataConstructor uid row tms
    ForeignValueIpld uid1 tys uid2  -> Just $ ForeignValue uid1 tys uid2
    LambdaIpld body                 -> Just $ Lambda [] body
    _                               -> Nothing

instance (IsUid uid, IsIpld a, IsIpld b) => IsIpld (Tm 'CONTINUATION uid a b) where
  toIpld = \case
    Application spine -> ApplicationIpld spine
    Case uid branches -> CaseIpld uid branches
    Handle adj peg handlers valHandler -> HandleIpld adj peg handlers valHandler
    Let pty _name scope -> LetIpld pty scope
  fromIpld = \case
    ApplicationIpld spine                  -> Just $ Application spine
    CaseIpld uid branches                  -> Just $ Case uid branches
    HandleIpld adj peg handlers valHandler -> Just $
      Handle adj peg handlers valHandler
    LetIpld pty scope                      -> Just $ Let pty "" scope
    _                                      -> Nothing

instance (IsUid uid, IsIpld a, IsIpld b) => IsIpld (Tm 'TM uid a b) where
  toIpld = \case
    Variable b                -> VariableIpld b
    InstantiatePolyVar b args -> InstantiatePolyVarIpld b args
    Annotation tm ty          -> AnnotationIpld tm ty
    Value tm                  -> ValueIpld tm
    Cut cont scrutinee        -> CutIpld cont scrutinee
    Letrec defns body         -> LetrecIpld defns body

  fromIpld = \case
    VariableIpld b                -> Just $ Variable b
    InstantiatePolyVarIpld b args -> Just $ InstantiatePolyVar b args
    AnnotationIpld tm ty          -> Just $ Annotation tm ty
    ValueIpld tm                  -> Just $ Value tm
    CutIpld cont scrutinee        -> Just $ Cut cont scrutinee
    LetrecIpld defns body         -> Just $ Letrec defns body
    _                             -> Nothing

instance (IsUid uid, IsIpld a, IsIpld b) => IsIpld (Tm 'ADJUSTMENT_HANDLERS uid a b) where
  toIpld (AdjustmentHandlers uidmap) = AdjustmentHandlersIpld uidmap
  fromIpld = \case
    AdjustmentHandlersIpld uidmap -> Just $ AdjustmentHandlers uidmap
    _                             -> Nothing

instance (IsUid uid, IsIpld a) => IsIpld (Polytype uid a)
instance (IsUid uid, IsIpld uid, IsIpld a) => IsIpld (Adjustment uid a)
instance (IsUid uid, IsIpld a) => IsIpld (ConstructorDecl uid a)
instance (IsUid uid, IsIpld a) => IsIpld (CommandDeclaration uid a)
instance IsIpld InitiateAbility
instance IsIpld Kind
instance IsIpld (DataTypeInterface Cid Int)
instance IsIpld (EffectInterface Cid Int)

-- Applicative / Monad

instance Applicative (ValTy uid) where pure = VariableTy; (<*>) = ap

instance Monad (ValTy uid) where
  return = VariableTy
  (>>=) = flip bindTy

-- This has a more general type than bind (`Ty 'VALTY uid a`)
bindTy :: (a -> ValTy uid b) -> Ty tag uid a -> Ty tag uid b
bindTy f = \case
  DataTy uid args -> DataTy uid ((bindTy f) <$> args)
  SuspendedTy (CompTy dom codom) ->
    let dom' = (bindTy f) <$> dom
        codom' = bindTy f codom
    in SuspendedTy (CompTy dom' codom')
  VariableTy a -> f a
  CompTy vals peg -> CompTy (bindTy f <$> vals) (bindTy f peg)
  TyArgVal a     -> TyArgVal (bindTy f a)
  TyArgAbility a -> TyArgAbility (bindTy f a)
  Ability initAbility uidMap ->
    Ability initAbility ((bindTy f) <$$> uidMap)
  Peg ab val -> Peg (bindTy f ab) (bindTy f val)

-- This has a more general type than bind (`Tm 'TM uid a`)
bindTm :: (a -> Tm 'TM uid c b) -> Tm tag uid c a -> Tm tag uid c b
bindTm f = \case
  Command uid row -> Command uid row
  DataConstructor uid row tms ->
    DataConstructor uid row ((>>= f) <$> tms)
  ForeignValue tyuid tysat valuid -> ForeignValue tyuid tysat valuid
  Lambda binderNames body -> Lambda binderNames (body >>>= f)

  Application spine -> Application ((>>= f) <$> spine)
  Case uid branches ->
    let bindBranch (binders, body) = (binders, body >>>= f)
    in Case uid (bindBranch <$> branches)
  Handle adj peg handlers rhs -> Handle
    adj
    peg
    (bindTm f handlers)
    (rhs >>>= f)
  Let poly name rhs -> Let poly name (rhs >>>= f)

  Variable a -> f a
  InstantiatePolyVar a _ -> f a
  Annotation val ty -> Annotation (bindTm f val) ty
  Value v -> Value (bindTm f v)
  Cut neg pos -> Cut (bindTm f neg) (pos >>= f)
  Letrec defns body -> Letrec
    -- (defns & traverse._2 (bindTm f))
    ((\(pty, tm) -> (pty, bindTm f tm)) <$> defns)
    (body >>>= f)
  AdjustmentHandlers handlers -> AdjustmentHandlers ((>>>= f) <$$> handlers)

instance Functor (Tm tag uid a) where fmap = fmapDefault
instance Foldable (Tm tag uid a) where foldMap = foldMapDefault

instance Traversable (Tm tag uid a) where
  traverse f = \case
    Command uid row -> pure (Command uid row)
    DataConstructor uid row tms -> DataConstructor uid row <$> (traverse . traverse) f tms
    ForeignValue uid1 tys uid2 -> pure (ForeignValue uid1 tys uid2)
    Lambda names body -> Lambda names <$> (traverse) f body

    Application spine -> Application <$> (traverse . traverse) f spine
    Case uid branches ->
      let f' (names, scope) = (names,) <$> traverse f scope
      in Case uid <$> traverse f' branches
    Handle adj peg handlers valHandler -> Handle adj peg
      <$> traverse f handlers <*> traverse f valHandler
    Let pty name body -> Let pty name <$> traverse f body

    Variable var -> Variable <$> f var
    InstantiatePolyVar var tys -> InstantiatePolyVar <$> f var <*> pure tys
    Annotation tm ty -> Annotation <$> traverse f tm <*> pure ty
    Value val -> Value <$> traverse f val
    Cut cont scrutinee -> Cut <$> traverse f cont <*> traverse f scrutinee
    Letrec defns body ->
      let f' (pty, defn) = (pty,) <$> traverse f defn
      in Letrec <$> traverse f' defns <*> traverse f body

    AdjustmentHandlers uidmap ->
      AdjustmentHandlers <$> (traverse . traverse . traverse) f uidmap

instance (IsUid uid, Eq a, Eq b) => Eq (Tm tag uid a b) where
  (==) = liftEq (==)
instance (IsUid uid, Ord a, Ord b) => Ord (Tm tag uid a b) where
  compare = liftCompare compare
instance (Show uid, Show a, Show b) => Show (Tm tag uid a b) where
  showsPrec = liftShowsPrec showsPrec showList
instance Applicative (Tm 'TM uid a) where pure = Variable; (<*>) = ap
instance Monad (Tm 'TM uid a) where
  return = Variable

  (>>=) = flip bindTm

-- Eq1

instance IsUid uid => Eq1 (Ty tag uid) where
  liftEq eq (DataTy uid1 args1) (DataTy uid2 args2)
    = uid1 == uid2 && liftEq (liftEq eq) args1 args2
  liftEq eq (SuspendedTy cty1) (SuspendedTy cty2) = liftEq eq cty1 cty2
  liftEq eq (VariableTy v1) (VariableTy v2) = eq v1 v2

  liftEq eq (CompTy dom1 codom1) (CompTy dom2 codom2)
    = liftEq (liftEq eq) dom1 dom2 && liftEq eq codom1 codom2

  liftEq eq (Peg ab1 val1) (Peg ab2 val2)
    = liftEq eq ab1 ab2 && liftEq eq val1 val2

  liftEq eq (TyArgVal val1) (TyArgVal val2) = liftEq eq val1 val2
  liftEq eq (TyArgAbility ab1) (TyArgAbility ab2) = liftEq eq ab1 ab2

  liftEq eq (Ability init1 entries1) (Ability init2 entries2) =
    init1 == init2 &&
    liftEq (liftEq (liftEq eq)) (toList entries1) (toList entries2)

  liftEq _ _ _ = False

instance IsUid uid => Eq1 (Polytype uid) where
  liftEq eq (Polytype binders1 val1) (Polytype binders2 val2) =
    let f (a, k1) (b, k2) = eq a b && k1 == k2
    in liftEq f binders1 binders2 && liftEq eq val1 val2

instance (IsUid uid, Eq e) => Eq1 (Tm tag uid e) where
  liftEq _ (Command uid1 row1) (Command uid2 row2) =
    uid1 == uid2 && row1 == row2
  liftEq eq (DataConstructor uid1 row1 app1) (DataConstructor uid2 row2 app2) =
    uid1 == uid2 && row1 == row2 && liftEq (liftEq eq) app1 app2
  liftEq _
    (ForeignValue tyuid1 sat1 valuid1)
    (ForeignValue tyuid2 sat2 valuid2) =
    tyuid1 == tyuid2 &&
    sat1 == sat2 &&
    valuid1 == valuid2
  liftEq eq (Lambda binderNames1 body1) (Lambda binderNames2 body2) =
    binderNames1 == binderNames2 &&
    liftEq eq body1 body2

  liftEq eq (Application spine1) (Application spine2) =
     liftEq (liftEq eq) spine1 spine2
  liftEq eq (Case uid1 rows1) (Case uid2 rows2) =
     let f (binders1, body1) (binders2, body2) =
           binders1 == binders2 &&
           liftEq eq body1 body2
     in uid1 == uid2 &&
        liftEq f (toList rows1) (toList rows2)
  liftEq eq (Handle adj1 peg1 handlers1 body1) (Handle adj2 peg2 handlers2 body2) =
     adj1 == adj2 &&
     peg1 == peg2 &&
     liftEq eq handlers1 handlers2 &&
     liftEq eq body1 body2
  liftEq eq (Let pty1 name1 body1) (Let pty2 name2 body2) =
     pty1 == pty2 && name1 == name2 && liftEq eq body1 body2

  liftEq eq (Variable a) (Variable b) = eq a b
  liftEq eq (InstantiatePolyVar var1 args1) (InstantiatePolyVar var2 args2)
    = eq var1 var2 && liftEq (liftEq (==)) args1 args2
  liftEq eq (Annotation tm1 ty1) (Annotation tm2 ty2)
    = liftEq eq tm1 tm2 && liftEq (==) ty1 ty2
  liftEq eq (Value v1) (Value v2)
    = liftEq eq v1 v2
  liftEq eq (Cut cont1 val1) (Cut cont2 val2)
    = liftEq eq cont1 cont2 && liftEq eq val1 val2
  liftEq eq (Letrec binders1 body1) (Letrec binders2 body2) =
    liftEq (liftEq (liftEq eq)) binders1 binders2 &&
    liftEq eq body1 body2

  liftEq eq (AdjustmentHandlers handlers1) (AdjustmentHandlers handlers2) =
    liftEq (liftEq (liftEq eq)) (toList handlers1) (toList handlers2)

  liftEq _ _ _ = False

-- Ord1

instance IsUid uid => Ord1 (Ty tag uid) where
  liftCompare cmp (Ability init1 entries1) (Ability init2 entries2) =
    compare init1 init2 <>
    liftCompare (liftCompare (liftCompare cmp))
      (toList entries1)
      (toList entries2)

  liftCompare cmp (Peg ab1 val1) (Peg ab2 val2) =
    liftCompare cmp ab1 ab2 <>
    liftCompare cmp val1 val2

  liftCompare cmp (CompTy vt1 p1) (CompTy vt2 p2) =
    liftCompare (liftCompare cmp) vt1 vt2 <>
    liftCompare cmp p1 p2

  liftCompare cmp (TyArgVal valTy1) (TyArgVal valTy2)
    = liftCompare cmp valTy1 valTy2
  liftCompare cmp (TyArgAbility ability1) (TyArgAbility ability2)
    = liftCompare cmp ability1 ability2

  liftCompare cmp (DataTy uid1 args1) (DataTy uid2 args2) =
      compare uid1 uid2 <> liftCompare (liftCompare cmp) args1 args2
  liftCompare cmp (SuspendedTy cty1) (SuspendedTy cty2) = liftCompare cmp cty1 cty2
  liftCompare cmp (VariableTy v1) (VariableTy v2) = cmp v1 v2

  liftCompare _ l r = compare (ordering l) (ordering r)
    -- This section is rather arbitrary
    where ordering :: Ty tag uid a -> Int
          ordering = \case
            DataTy{}       -> 0
            SuspendedTy{}  -> 1
            VariableTy{}   -> 2
            CompTy{}       -> 3
            Peg{}          -> 4
            TyArgVal{}     -> 5
            TyArgAbility{} -> 6
            Ability{}      -> 7

instance (IsUid uid, Ord o) => Ord1 (Tm tag uid o) where
  liftCompare _cmp (Command uid1 row1) (Command uid2 row2) =
    compare uid1 uid2 <>
    compare row1 row2
  liftCompare cmp (DataConstructor uid1 row1 app1) (DataConstructor uid2 row2 app2) =
    compare uid1 uid2 <>
    compare row1 row2 <>
    liftCompare (liftCompare cmp) app1 app2
  liftCompare _cmp (ForeignValue tyuid1 sat1 valuid1) (ForeignValue tyuid2 sat2 valuid2) =
    compare tyuid1 tyuid2 <>
    compare sat1 sat2 <>
    compare valuid1 valuid2
  liftCompare cmp (Lambda binderNames1 body1) (Lambda binderNames2 body2) =
    compare binderNames1 binderNames2 <>
    liftCompare cmp body1 body2

  liftCompare cmp (Application spine1) (Application spine2) =
    liftCompare (liftCompare cmp) spine1 spine2
  liftCompare cmp (Case uid1 rows1) (Case uid2 rows2) =
    let f (binders1, body1) (binders2, body2) =
          compare binders1 binders2 <> liftCompare cmp body1 body2
    in compare uid1 uid2 <>
       liftCompare f (toList rows1) (toList rows2)
  liftCompare cmp (Handle adj1 peg1 handlers1 body1) (Handle adj2 peg2 handlers2 body2) =
    compare adj1 adj2 <>
    compare peg1 peg2 <>
    liftCompare cmp handlers1 handlers2 <>
    liftCompare cmp body1 body2
  liftCompare cmp (Let pty1 name1 body1) (Let pty2 name2 body2) =
    compare pty1 pty2 <> compare name1 name2 <> liftCompare cmp body1 body2

  liftCompare cmp (Variable a) (Variable b) = cmp a b
  liftCompare cmp (InstantiatePolyVar var1 args1) (InstantiatePolyVar var2 args2)
    = cmp var1 var2 <> liftCompare (liftCompare compare) args1 args2
  liftCompare cmp (Annotation tm1 ty1) (Annotation tm2 ty2)
    = liftCompare cmp tm1 tm2 <> liftCompare compare ty1 ty2
  liftCompare cmp (Value v1) (Value v2)
    = liftCompare cmp v1 v2
  liftCompare cmp (Cut cont1 val1) (Cut cont2 val2)
    = liftCompare cmp cont1 cont2 <> liftCompare cmp val1 val2
  liftCompare cmp (Letrec binders1 body1) (Letrec binders2 body2)
    = liftCompare (liftCompare (liftCompare cmp)) binders1 binders2 <>
      liftCompare cmp body1 body2

  liftCompare cmp (AdjustmentHandlers handlers1) (AdjustmentHandlers handlers2)
    = liftCompare (liftCompare (liftCompare cmp))
        (toList handlers1)
        (toList handlers2)

  liftCompare _ x y = compare (ordering x) (ordering y) where
    ordering :: Tm tag uid a b -> Int
    ordering = \case
      Command{}            -> 0
      DataConstructor{}    -> 1
      ForeignValue{}       -> 2
      Lambda{}             -> 3
      Application{}        -> 4
      Case{}               -> 5
      Handle{}             -> 6
      Let{}                -> 7
      Variable{}           -> 8
      InstantiatePolyVar{} -> 9
      Annotation{}         -> 10
      Value{}              -> 11
      Cut{}                -> 12
      Letrec{}             -> 13
      AdjustmentHandlers{} -> 14

-- Show1

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
      . liftShowsPrec s sl 11 ab

instance Show uid => Show1 (Ability uid) where
  liftShowsPrec s sl d (Ability initAbility uidMap) = showParen (d > 10) $
      showString "Ability "
    . shows initAbility
    . showSpace
    . liftShowList (liftShowsPrec s sl) (liftShowList s sl) (toList uidMap)

instance Show uid => Show1 (CompTy uid) where
  liftShowsPrec s sl d (CompTy dom codom) = showParen (d > 10) $
      showString "CompTy "
    . liftShowList s sl dom
    . showSpace
    . liftShowsPrec s sl 11 codom

instance Show uid => Show1 (Peg uid) where
  liftShowsPrec s sl d (Peg ab val) = showParen (d > 10) $
      showString "Peg "
    . liftShowsPrec s sl 11 ab
    . showSpace
    . liftShowsPrec s sl 11 val

instance (Show uid, Show a) => Show1 (Tm tag uid a) where
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
      . showSpace
      . liftShowList s sl tms
    ForeignValue tyuid sat valuid ->
        showString "ForeignValue "
      . shows tyuid
      . showSpace
      . showList sat
      . showSpace
      . shows valuid
    Lambda binderNames scope ->
        showString "Lambda "
      . showList binderNames
      . liftShowsPrec s sl 11 scope
    Application spine ->
        showString "Application "
      . liftShowList s sl spine
    Case uid branches ->
        showString "Case "
      . shows uid
      . showSpace
      . liftShowList s sl (snd <$> branches)
    Handle adj peg handlers body ->
        showString "Handle "
      . showsPrec 11 adj
      . showSpace
      . showsPrec 11 peg
      . showSpace
      . liftShowsPrec s sl 11 handlers
      . showSpace
      . liftShowsPrec s sl 11 body
    Let pty name body ->
        showString "Let"
      . showsPrec 11 pty
      . showSpace
      . shows name
      . showSpace
      . liftShowsPrec s sl 11 body
    Variable b ->
        showString "Variable "
      . s 11 b
    InstantiatePolyVar b tys ->
        showString "InstantiatePolyVar "
      . s 11 b
      . showSpace
      . shows tys
    Annotation tm valTy ->
        showString "Annotation "
      . liftShowsPrec s sl 11 tm
      . showSpace
      . showsPrec 11 valTy
    Value val' ->
        showString "Value "
      . liftShowsPrec s sl 11 val'
    Cut cont scrutinee ->
        showString "Cut "
      . liftShowsPrec s sl 11 cont
      . showSpace
      . liftShowsPrec s sl 11 scrutinee
    Letrec defns body ->
        showString "Letrec "
      . liftShowList (liftShowsPrec s sl) (liftShowList s sl) defns
      . showSpace
      . liftShowsPrec s sl 11 body

    AdjustmentHandlers uidMap ->
        showString "AdjustmentHandlers "
      . liftShowList (liftShowsPrec s sl) (liftShowList s sl) (toList uidMap)

-- Lens Hell:

makeLenses ''EffectInterface
makeLenses ''ResolvedDecls
makeLenses ''DataTypeInterface
