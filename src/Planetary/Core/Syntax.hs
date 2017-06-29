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
{-# language OverloadedStrings #-}
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
import Control.Unification
import Data.Data
import Data.Foldable (toList)
import Data.Functor.Classes
import Data.Functor.Fixedpoint
import qualified Data.HashMap.Strict as HashMap
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

data Kind = ValTyK | EffTyK
  deriving (Show, Eq, Ord, Typeable, Generic)

data Ty uid ty
  -- ValTy
  = DataTy_ !uid !(Vector ty)
  | SuspendedTy_ !ty
  | BoundVariableTy_ !Int
  | FreeVariableTy_ !Text

  -- CompTy
  | CompTy_ !(Vector ty) !ty

  -- Peg
  | Peg_ !ty !ty

  -- TyArg
  | TyArgVal_ !ty
  | TyArgAbility_ !ty

  -- Ability
  -- "For each UID, instantiate it with these args"
  | Ability_ !InitiateAbility !(UIdMap uid (Vector ty))
  deriving (Eq, Show, Ord, Typeable, Functor, Foldable, Traversable)

instance IsUid uid => Unifiable (Ty uid) where
  zipMatch (DataTy_ uid1 args1) (DataTy_ uId2 args2) =
    if uid1 == uId2 && length args1 == length args2
    then Just $ DataTy_ uid1 (Right <$> zip args1 args2)
    else Nothing
  zipMatch (SuspendedTy_ cty1) (SuspendedTy_ cty2)
    = Just (SuspendedTy_ (Right (cty1, cty2)))

  zipMatch (BoundVariableTy_ a) (BoundVariableTy_ b)
    = if a == b then Just (BoundVariableTy_ a) else Nothing

  zipMatch (FreeVariableTy_ a) (FreeVariableTy_ b)
    = if a == b then Just (FreeVariableTy_ a) else Nothing

  zipMatch (CompTy_ as a) (CompTy_ bs b) =
    if length as == length bs
    then Just $ CompTy_ (Right <$> zip as bs) (Right (a, b))
    else Nothing

  zipMatch (Peg_ ty11 ty12) (Peg_ ty21 ty22)
    = Just (Peg_ (Right (ty11, ty21)) (Right (ty12, ty22)))

  zipMatch (TyArgVal_ ty1) (TyArgVal_ ty2)
    = Just (TyArgVal_ (Right (ty1, ty2)))
  zipMatch (TyArgAbility_ ty1) (TyArgAbility_ ty2)
    = Just (TyArgAbility_ (Right (ty1, ty2)))

  zipMatch (Ability_ init1 (UIdMap tyArgs1)) (Ability_ init2 (UIdMap tyArgs2)) = do
    let onlyInLeft  = HashMap.difference tyArgs1 tyArgs2
        onlyInRight = HashMap.difference tyArgs2 tyArgs1
        unifyTyArgVec args1 args2 =
          if length args1 == length args2
          then Just $ Right <$> zip args1 args2
          else Nothing

    boths <- sequence $ HashMap.intersectionWith unifyTyArgVec tyArgs1 tyArgs2

    let mergedTyArgs = UIdMap $ HashMap.unions
          [Left <$$> onlyInLeft, Left <$$> onlyInRight, boths]
        leftOnly  = Just $ Ability_ ClosedAbility (Left <$$> UIdMap tyArgs1)
        rightOnly = Just $ Ability_ ClosedAbility (Left <$$> UIdMap tyArgs2)

    case (init1, init2) of
      (OpenAbility, OpenAbility) -> Just $ Ability_ OpenAbility mergedTyArgs
      (OpenAbility, ClosedAbility) ->
        if HashMap.null onlyInLeft then leftOnly else Nothing
      (ClosedAbility, OpenAbility) ->
        if HashMap.null onlyInRight then rightOnly else Nothing
      (ClosedAbility, ClosedAbility) ->
        Just $ Ability_ ClosedAbility (UIdMap boths)

  zipMatch _ _ = Nothing

type UTy = UTerm (Ty Cid)

-- The rest of the signatures are similar
pattern DataTyU :: Cid -> Vector (UTy var) -> UTy var
pattern DataTyU uid args   = UTerm (DataTy_ uid args)
pattern SuspendedTyU ty    = UTerm (SuspendedTy_ ty)
pattern CompTyU dom codom  = UTerm (CompTy_ dom codom)
pattern PegU dom codom     = UTerm (Peg_ dom codom)
pattern TyArgValU ty       = UTerm (TyArgVal_ ty)
pattern TyArgAbilityU ab   = UTerm (TyArgAbility_ ab)
pattern AbilityU init args = UTerm (Ability_ init args)
pattern BoundVariableTyU v = UTerm (BoundVariableTy_ v)
pattern FreeVariableTyU v  = UTerm (FreeVariableTy_ v)
pattern VariableTyU v      = UVar v

type TyFix uid = Fix (Ty uid)
type TyFix' = TyFix Cid

type ValTy   uid = TyFix uid
type TyArg   uid = TyFix uid
type Ability uid = TyFix uid
type CompTy  uid = TyFix uid
type Peg     uid = TyFix uid

-- The rest of the signatures are similar
pattern DataTy :: uid -> Vector (TyFix uid) -> TyFix uid
pattern DataTy uid args   = Fix (DataTy_ uid args)
pattern SuspendedTy ty    = Fix (SuspendedTy_ ty)
pattern CompTy dom codom  = Fix (CompTy_ dom codom)
pattern Peg dom codom     = Fix (Peg_ dom codom)
pattern TyArgVal ty       = Fix (TyArgVal_ ty)
pattern TyArgAbility ab   = Fix (TyArgAbility_ ab)
pattern Ability init args = Fix (Ability_ init args)
pattern BoundVariableTy v = Fix (BoundVariableTy_ v)
pattern FreeVariableTy v  = Fix (FreeVariableTy_ v)

data Polytype uid = Polytype
  -- Universally quantify over a bunch of variables
  { polyBinders :: !(Vector (Text, Kind))
  -- resulting in a value type
  , polyVal :: !(TyFix uid)
  } deriving (Typeable, Generic)

instance Show uid => Show (Polytype uid) where
  showsPrec d (Polytype binders val) = showParen (d > 10) $
      showString "Polytype "
    . showList binders
    . showString " "
    . showsPrec 11 val

instance Eq uid => Eq (Polytype uid) where
  Polytype binders1 val1 == Polytype binders2 val2
    = binders1 == binders2 && val1 == val2

instance IsUid uid => Ord (Polytype uid) where
  compare (Polytype binders1 val1) (Polytype binders2 val2)
    = compare binders1 binders2 <> compare val1 val2

data ConstructorDecl uid = ConstructorDecl
  { _constructorName   :: !Text
  , _constructorArgs   :: !(Vector (ValTy uid))
  , _constructorResult :: !(Vector (TyArg uid))
  }
  deriving (Show, Eq, Ord, Typeable, Generic)

-- A collection of data constructor signatures (which can refer to bound type /
-- effect variables).
data DataTypeInterface uid = DataTypeInterface
  -- we universally quantify over some number of type variables
  { _dataBinders :: !(Vector (Text, Kind))
  -- a collection of constructors taking some arguments
  , _constructors :: !(Vector (ConstructorDecl uid))
  } deriving (Show, Eq, Ord, Typeable, Generic)

emptyDataTypeInterface :: DataTypeInterface uid
emptyDataTypeInterface = DataTypeInterface [] []

-- commands take arguments (possibly including variables) and return a value
--
-- TODO: maybe rename this to `Command` if we do reuse it in instantiateAbility
data CommandDeclaration uid = CommandDeclaration
  { _commandName :: !Text
  , _commandArgs :: !(Vector (ValTy uid))
  , _commandRet :: !(ValTy uid)
  } deriving (Show, Eq, Ord, Typeable, Generic)

data EffectInterface uid = EffectInterface
  -- we universally quantify some number of type variables
  { _interfaceBinders :: !(Vector (Text, Kind))
  -- a collection of commands
  , _commands :: !(Vector (CommandDeclaration uid))
  } deriving (Show, Eq, Ord, Typeable, Generic)

-- An adjustment is a mapping from effect inferface id to the types it's
-- applied to. IE a set of saturated interfaces.
newtype Adjustment uid = Adjustment
  { unAdjustment :: UIdMap uid (Vector (TyArg uid)) }
  deriving (Monoid, Show, Eq, Ord, Typeable, Generic)

-- Terms

data TmTag
  = VALUE
  | CONTINUATION
  | TM
  | ADJUSTMENT_HANDLERS

data Tm (tag :: TmTag) uid b where
  -- Term:
  -- use (inferred)
  Command :: !uid -> !Row -> Tm 'VALUE uid b

  -- construction (checked)
  DataConstructor
    :: !uid
    -> !Row
    -> !(Vector (Tm 'TM uid b)) -> Tm 'VALUE uid b
  ForeignValue :: !uid -> !(Vector (ValTy uid)) -> !uid -> Tm 'VALUE uid b
  Lambda :: !(Vector Text) -> !(Scope Int (Tm 'TM uid ) b) -> Tm 'VALUE uid b

  -- Continuation:
  -- use (inferred)
  Application :: !(Spine uid b) -> Tm 'CONTINUATION uid b

  -- construction (checked)
  Case
    :: !uid
    -> !(Vector (Vector Text, Scope Int (Tm 'TM uid) b))
    -> Tm 'CONTINUATION uid b
  Handle
    :: !(Adjustment uid)
    -> !(Peg uid)
    -> !(Tm 'ADJUSTMENT_HANDLERS uid b)
    -> !(Scope () (Tm 'TM uid) b)
    -> Tm 'CONTINUATION uid b
  Let
    :: !(Polytype uid)
    -> !Text
    -> !(Scope () (Tm 'TM uid) b)
    -> Tm 'CONTINUATION uid b

  -- Term
  Variable :: !b -> Tm 'TM uid b

  InstantiatePolyVar :: !b -> !(Vector (TyArg uid)) -> Tm 'TM uid b
  Annotation :: !(Tm 'VALUE uid b) -> !(ValTy uid) -> Tm 'TM uid b
  Value :: !(Tm 'VALUE uid b) -> Tm 'TM uid b
  Cut :: !(Tm 'CONTINUATION uid b) -> !(Tm 'TM uid b) -> Tm 'TM uid b
  Letrec
    -- invariant: each value is a lambda
    :: !(Vector (Polytype uid, Tm 'VALUE uid b))
    -> !(Scope Int (Tm 'TM uid) b)
    -> Tm 'TM uid b

  -- Other
  -- Adjustment handlers are a mapping from effect interface id to the handlers
  -- for each of that interface's constructors.
  --
  -- Encode each constructor argument (x_c) as a `Just Int` and the
  -- continuation (z_c) as `Nothing`.
  AdjustmentHandlers
    :: !(UIdMap uid (Vector (Scope (Maybe Int) (Tm 'TM uid) b)))
    -> Tm 'ADJUSTMENT_HANDLERS uid b

-- type? newtype?
type Spine uid b = Vector (Tm 'TM uid b)

data Decl uid b
  = DataDecl_      !(DataDecl uid)
  | InterfaceDecl_ !(InterfaceDecl uid)
  | TermDecl_      !(TermDecl uid b)
  deriving (Eq, Ord, Show, Typeable, Generic)

data DataDecl uid = DataDecl !Text !(DataTypeInterface uid)
  deriving (Eq, Ord, Show, Typeable, Generic)

data InterfaceDecl uid = InterfaceDecl !Text !(EffectInterface uid)
  deriving (Eq, Ord, Show, Typeable, Generic)

data TermDecl uid b = TermDecl
  !Text           -- ^ the term's name
  !(Tm 'TM uid b) -- ^ body
  deriving (Typeable, Generic)

deriving instance (IsUid uid, Eq b) => Eq (TermDecl uid b)
deriving instance (IsUid uid, Ord b) => Ord (TermDecl uid b)
deriving instance (Show uid, Show b) => Show (TermDecl uid b)

type DeclS          = Decl          Text Text
type DataDeclS      = DataDecl      Text
type InterfaceDeclS = InterfaceDecl Text
type TermDeclS      = TermDecl      Text Text

data ResolvedDecls = ResolvedDecls
  { _datatypes  :: !(UIdMap Cid DataTypeInterfaceI)
  , _interfaces :: !(UIdMap Cid EffectInterfaceI)
  , _globalCids :: ![(Text, Cid)]
  , _terms      :: ![Executable2 TermDecl]
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

closedAbility :: IsUid uid => Ability uid
closedAbility = Ability ClosedAbility mempty

emptyAbility :: IsUid uid => Ability uid
emptyAbility = Ability OpenAbility mempty

extendAbility
  :: IsUid uid
  => Ability uid
  -> Adjustment uid
  -> Ability uid
extendAbility (Ability initAb uidMap) (Adjustment adj)
  = Ability initAb (uidMap `uidMapUnion` adj)
extendAbility _ _ = error "extendAbility called with non-ability"

-- executable

type Executable1 f = f Cid
type Executable2 f = f Cid Int

type AbilityI            = Ability Cid
type AdjustmentI         = Adjustment Cid
type CommandDeclarationI = Executable1 CommandDeclaration
type CompTyI             = CompTy Cid
type PolytypeI           = Polytype Cid
type ValTyI              = ValTy Cid
type TyArgI              = TyArg Cid
type DataTypeInterfaceI  = Executable1 DataTypeInterface
type EffectInterfaceI    = Executable1 EffectInterface
type ConstructorDeclI    = Executable1 ConstructorDecl
type PegI                = Peg Cid

type TmI                 = Executable2 (Tm 'TM)
type ValueI              = Executable2 (Tm 'VALUE)
type ContinuationI       = Executable2 (Tm 'CONTINUATION)
type AdjustmentHandlersI = Executable2 (Tm 'ADJUSTMENT_HANDLERS)
type SpineI              = Spine Cid Int
type UseI                = TmI
type ConstructionI       = TmI

-- raw

type Raw1 f = f Text
type Raw2 f = f Text Text

type Ability'            = Ability Text
type Adjustment'         = Adjustment Text
type CommandDeclaration' = Raw1 CommandDeclaration
type CompTy'             = CompTy Text
type ConstructorDecl'    = Raw1 ConstructorDecl
type Peg'                = Peg Text
type Polytype'           = Polytype Text
type TyArg'              = TyArg Text
type ValTy'              = ValTy Text

type Tm'                 = Raw2 (Tm 'TM)
type Value'              = Raw2 (Tm 'VALUE)
type Continuation'       = Raw2 (Tm 'CONTINUATION)
type AdjustmentHandlers' = Raw2 (Tm 'ADJUSTMENT_HANDLERS)
type Spine'              = Spine Text Text
type Construction        = Tm'
type Use                 = Tm'
type Cont'               = Continuation'

-- utils:

-- | abstract 0 variables
abstract0 :: Monad f => f a -> Scope b f a
abstract0 = abstract
  (error "abstract0 being used to instantiate > 0 variables")

closeVar :: Eq a => (a, b) -> Tm 'TM uid a -> Maybe (Tm 'TM uid b)
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
pattern BoundVariableTyIpld var = T1 "BoundVariableTy" var
pattern FreeVariableTyIpld var  = T1 "FreeVariableTy" var
pattern CompTyIpld dom codom    = T2 "CompTy" dom codom
pattern PegIpld ab ty           = T2 "Peg" ab ty
pattern TyArgValIpld ty         = T1 "TyArgVal" ty
pattern TyArgAbilityIpld ab     = T1 "TyArgAbility" ab
pattern AbilityIpld init uidmap = T2 "Ability" init uidmap

instance IsUid uid => IsIpld (TyFix uid) where
  toIpld = \case
    DataTy uid args     -> DataTyIpld uid args
    SuspendedTy cty     -> SuspendedTyIpld cty
    BoundVariableTy var -> BoundVariableTyIpld var
    FreeVariableTy var  -> FreeVariableTyIpld var
    CompTy dom codom    -> CompTyIpld dom codom
    Peg ab ty           -> PegIpld ab ty
    TyArgVal ty         -> TyArgValIpld ty
    TyArgAbility ab     -> TyArgAbilityIpld ab
    Ability i uidmap    -> AbilityIpld i uidmap
    _                   -> error
      "toIpld (FyFix uid) called with impossible value"

  fromIpld = \case
    DataTyIpld uid args     -> Just $ DataTy uid args
    SuspendedTyIpld cty     -> Just $ SuspendedTy cty
    BoundVariableTyIpld var -> Just $ SuspendedTy var
    FreeVariableTyIpld var  -> Just $ SuspendedTy var
    CompTyIpld dom codom    -> Just $ CompTy dom codom
    PegIpld ab ty           -> Just $ Peg ab ty
    TyArgValIpld ty         -> Just $ TyArgVal ty
    TyArgAbilityIpld ab     -> Just $ TyArgAbility ab
    AbilityIpld i uidmap    -> Just $ Ability i uidmap
    _                       -> Nothing

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

instance (IsUid uid, IsIpld b) => IsIpld (Tm 'VALUE uid b) where
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

instance (IsUid uid, IsIpld b) => IsIpld (Tm 'CONTINUATION uid b) where
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

instance (IsUid uid, IsIpld b) => IsIpld (Tm 'TM uid b) where
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

instance (IsUid uid, IsIpld b) => IsIpld (Tm 'ADJUSTMENT_HANDLERS uid b) where
  toIpld (AdjustmentHandlers uidmap) = AdjustmentHandlersIpld uidmap
  fromIpld = \case
    AdjustmentHandlersIpld uidmap -> Just $ AdjustmentHandlers uidmap
    _                             -> Nothing

instance IsUid uid => IsIpld (Polytype uid)
instance (IsUid uid, IsIpld uid) => IsIpld (Adjustment uid)
instance (IsUid uid) => IsIpld (ConstructorDecl uid)
instance (IsUid uid) => IsIpld (CommandDeclaration uid)
instance IsIpld InitiateAbility
instance IsIpld Kind
instance IsIpld (DataTypeInterface Cid)
instance IsIpld (EffectInterface Cid)

-- Applicative / Monad

-- -- This has a more general type than bind (`Tm 'TM uid a`)
bindTm :: (a -> Tm 'TM uid b) -> Tm tag uid a -> Tm tag uid b
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
    (defns & traverse._2 %~ bindTm f)
    (body >>>= f)
  AdjustmentHandlers handlers -> AdjustmentHandlers ((>>>= f) <$$> handlers)

instance Functor (Tm tag uid) where fmap = fmapDefault
instance Foldable (Tm tag uid) where foldMap = foldMapDefault

instance Traversable (Tm tag uid) where
  traverse f = \case
    Command uid row -> pure (Command uid row)
    DataConstructor uid row tms -> DataConstructor uid row <$> (traverse . traverse) f tms
    ForeignValue uid1 tys uid2 -> pure (ForeignValue uid1 tys uid2)
    Lambda names body -> Lambda names <$> traverse f body

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

instance (IsUid uid, Eq b) => Eq (Tm tag uid b) where
  (==) = liftEq (==)
instance (IsUid uid, Ord b) => Ord (Tm tag uid b) where
  compare = liftCompare compare
instance (Show uid, Show b) => Show (Tm tag uid b) where
  showsPrec = liftShowsPrec showsPrec showList
instance Applicative (Tm 'TM uid) where pure = Variable; (<*>) = ap
instance Monad (Tm 'TM uid) where
  return = Variable

  (>>=) = flip bindTm

-- Eq1

instance (IsUid uid) => Eq1 (Tm tag uid) where
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
    = eq var1 var2 && liftEq (==) args1 args2
  liftEq eq (Annotation tm1 ty1) (Annotation tm2 ty2)
    = liftEq eq tm1 tm2 && ty1 == ty2
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

instance (IsUid uid) => Ord1 (Tm tag uid) where
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
    = cmp var1 var2 <> liftCompare compare args1 args2
  liftCompare cmp (Annotation tm1 ty1) (Annotation tm2 ty2)
    = liftCompare cmp tm1 tm2 <> compare ty1 ty2
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
    ordering :: Tm tag uid b -> Int
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

instance (Show uid) => Show1 (Tm tag uid) where
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
