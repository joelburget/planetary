{-# language ApplicativeDo #-}
{-# language DataKinds #-}
{-# language DeriveDataTypeable #-}
{-# language DeriveFoldable #-}
{-# language DeriveFunctor #-}
{-# language DeriveGeneric #-}
{-# language DeriveTraversable #-}
{-# language FlexibleInstances #-}
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

import Control.Lens hiding (ix)
import qualified Control.Lens as Lens
import Control.Lens.TH (makeLenses)
import Control.Unification
import Data.Data
import Data.Functor.Fixedpoint
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Map (Map)
import Data.Semigroup ((<>))
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Data.Traversable (for)
import GHC.Generics
import Network.IPLD hiding (Row)

import Planetary.Core.UIdMap
import Planetary.Util

-- TODO:
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
  = DataTy_ !ty !(Vector ty)
  | SuspendedTy_ !ty
  | VariableTy_ !Text
  | UidTy_ !uid

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
  zipMatch (DataTy_ uid1 args1) (DataTy_ uid2 args2) =
    if length args1 == length args2
    then Just $ DataTy_ (Right (uid1, uid2)) (Right <$> zip args1 args2)
    else Nothing
  zipMatch (SuspendedTy_ cty1) (SuspendedTy_ cty2)
    = Just (SuspendedTy_ (Right (cty1, cty2)))

  zipMatch (VariableTy_ a) (VariableTy_ b)
    = if a == b then Just (VariableTy_ a) else Nothing

  zipMatch (UidTy_ a) (UidTy_ b)
    = if a == b then Just (UidTy_ a) else Nothing

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
pattern DataTyU :: UTy var -> Vector (UTy var) -> UTy var
pattern DataTyU uid args   = UTerm (DataTy_ uid args)
pattern SuspendedTyU ty    = UTerm (SuspendedTy_ ty)
pattern CompTyU dom codom  = UTerm (CompTy_ dom codom)
pattern PegU dom codom     = UTerm (Peg_ dom codom)
pattern TyArgValU ty       = UTerm (TyArgVal_ ty)
pattern TyArgAbilityU ab   = UTerm (TyArgAbility_ ab)
pattern AbilityU init args = UTerm (Ability_ init args)
pattern VariableTyU v      = UTerm (VariableTy_ v)
pattern UidTyU uid         = UTerm (UidTy_ uid)

type TyFix uid = Fix (Ty uid)
type TyFix' = TyFix Cid

type ValTy   uid = TyFix uid
type TyArg   uid = TyFix uid
type Ability uid = TyFix uid
type CompTy  uid = TyFix uid
type Peg     uid = TyFix uid

-- The rest of the signatures are similar
pattern DataTy :: TyFix uid -> Vector (TyFix uid) -> TyFix uid
pattern DataTy uid args   = Fix (DataTy_ uid args)
pattern SuspendedTy ty    = Fix (SuspendedTy_ ty)
pattern CompTy dom codom  = Fix (CompTy_ dom codom)
pattern Peg dom codom     = Fix (Peg_ dom codom)
pattern TyArgVal ty       = Fix (TyArgVal_ ty)
pattern TyArgAbility ab   = Fix (TyArgAbility_ ab)
pattern Ability init args = Fix (Ability_ init args)
pattern VariableTy v      = Fix (VariableTy_ v)
pattern UidTy v           = Fix (UidTy_ v)

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

-- Note: we're not really being careful enough here with the term / value
-- distinction. A value which isn't fully evaluated isn't really a value, even
-- though our predicates will say it is.
data TmF uid tm
  -- The first section is the values (or rather, terms which can be values):
  -- . uses (inferred)
  = Variable_ !Text
  | InstantiatePolyVar_ !tm            !(Vector (TyArg uid))
  | Command_            !uid           !Row
  | Annotation_         !tm            !(ValTy uid)

  -- . constructions (checked)
  | DataConstructor_    !uid           !Row                  !(Vector tm)
  | ForeignValue_
    !uid -- ^ type id
    !(Vector (ValTy uid))
    !uid -- ^ value locator
  | Lambda_             !(Vector Text) !tm

  -- Computations:
  -- . uses (inferred)
  | Application_ !tm !(Spine' tm)

  -- . constructions (checked)
  | Case_ !tm !(Vector (Vector Text, tm))
  | Handle_
    !tm
    !(Adjustment uid)
    !(Peg uid)
    !(UIdMap uid (Vector (Vector Text, Text, tm)))
    !(Text, tm)
  | Let_ !tm !(Polytype uid) !Text !tm
  -- invariant: each value in a letrec is a lambda
  -- TODO: we probably want to just bind directly instead of using a lambda
  | Letrec_
    !(Vector Text)               -- ^ the name of each fn
    !(Vector (Polytype uid, tm)) -- ^ a typed lambda
    !tm                          -- ^ the body

  -- Other:
  -- We syntactically distinguish terms from values in evaluation. This form is
  -- only used in the focus of the machine to mark it as a value.
  | Value_ !tm

  -- associate var to address
  -- TODO: Map gives us Ord, whereas HashMap doesn't...
  -- TODO: maybe rename to DeferredSubst
  | Closure_ !(Vector Text) !(Map Text uid) !tm

  -- This form is only used in evaluation to create a one-hole context
  | Hole_
  deriving (Eq, Ord, Show, Typeable, Generic, Functor, Foldable, Traversable)

pattern DataConstructor uid row tms
  = Fix (DataConstructor_ uid row tms)
pattern ForeignValue uid1 rows uid2
  = Fix (ForeignValue_ uid1 rows uid2)
pattern Lambda names body
  = Fix (Lambda_ names body)
pattern Application tm spine
  = Fix (Application_ tm spine)
pattern Case tm rows
  = Fix (Case_ tm rows)
pattern Handle tm adj peg handlers valHandler
  = Fix (Handle_ tm adj peg handlers valHandler)
pattern Let body pty name rhs
  = Fix (Let_ body pty name rhs)
pattern Variable name
  = Fix (Variable_ name)
pattern InstantiatePolyVar tm tyargs
  = Fix (InstantiatePolyVar_ tm tyargs)
pattern Command uid row
  = Fix (Command_ uid row)
pattern Annotation tm ty
  = Fix (Annotation_ tm ty)
pattern Letrec names lambdas body
  = Fix (Letrec_ names lambdas body)
pattern Value val
  = Fix (Value_ val)
pattern Closure names env tm
  = Fix (Closure_ names env tm)
pattern Hole
  = Fix Hole_

data Spine' tm = MixedSpine
  ![tm] -- ^ non-normalized terms
  ![tm] -- ^ normalized values
  deriving (Eq, Ord, Show, Typeable, Generic, Functor, Foldable, Traversable)

-- a few common type synonyms

type CommandDeclarationI = CommandDeclaration Cid
type PolytypeI           = Polytype Cid
type ValTyI              = ValTy Cid
type TyArgI              = TyArg Cid
type DataTypeInterfaceI  = DataTypeInterface Cid
type EffectInterfaceI    = EffectInterface Cid
type TmI                 = Tm Cid
type Spine               = Spine' TmI

instance IsIpld tm => IsIpld (Spine' tm)

pattern TermSpine :: [Tm uid] -> Spine' (Tm uid)
pattern TermSpine tms = MixedSpine tms []

pattern NormalSpine :: [Tm uid] -> Spine' (Tm uid)
pattern NormalSpine vals = MixedSpine [] vals

type Tm uid = Fix (TmF uid)

data Decl uid
  = DataDecl_      !(DataDecl uid)
  | InterfaceDecl_ !(InterfaceDecl uid)
  | TermDecl_      !(TermDecl uid)
  deriving (Eq, Ord, Show, Typeable, Generic)

data DataDecl uid = DataDecl !Text !(DataTypeInterface uid)
  deriving (Eq, Ord, Show, Typeable, Generic)

data InterfaceDecl uid = InterfaceDecl !Text !(EffectInterface uid)
  deriving (Eq, Ord, Show, Typeable, Generic)

data TermDecl uid = TermDecl
  !Text     -- ^ the term's name
  !(Tm uid) -- ^ body
  deriving (Eq, Ord, Show, Typeable, Generic)

data ResolvedDecls = ResolvedDecls
  { _datatypes  :: !(UIdMap Cid DataTypeInterfaceI)
  , _interfaces :: !(UIdMap Cid EffectInterfaceI)
  , _terms      :: !(UIdMap Cid TmI)
  , _globalCids :: !(HashMap Text Cid)
  } deriving Show

instance Monoid ResolvedDecls where
  mempty = ResolvedDecls mempty mempty mempty mempty
  ResolvedDecls d1 i1 t1 c1 `mappend` ResolvedDecls d2 i2 t2 c2
    = ResolvedDecls (d1 <> d2) (i1 <> i2) (t1 <> t2) (c1 <> c2)

makeLenses ''EffectInterface
makeLenses ''ResolvedDecls
makeLenses ''ConstructorDecl
makeLenses ''DataTypeInterface

-- TODO: make traversals
-- namedData :: Text -> Traversal' ResolvedDecls DataTypeInterfaceI
-- namedInterface :: Text -> Traversal' ResolvedDecls EffectInterfaceI

namedData :: Text -> ResolvedDecls -> Maybe (Cid, DataTypeInterfaceI)
namedData name decls = do
  cid <- decls ^? globalCids . Lens.ix name
  (cid,) <$> _datatypes decls ^? Lens.ix cid

namedInterface :: Text -> ResolvedDecls -> Maybe (Cid, EffectInterfaceI)
namedInterface name decls = do
  cid <- decls ^? globalCids . Lens.ix name
  (cid,) <$> _interfaces decls ^? Lens.ix cid

namedInterfaces :: [Text] -> ResolvedDecls -> Maybe [(Cid, EffectInterfaceI)]
namedInterfaces names decls = sequence (flip namedInterface decls <$> names)

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
  = Ability initAb (uidMap <> adj)
extendAbility _ _ = error "extendAbility called with non-ability"

-- $ Judgements

isValue :: Tm a -> Bool
isValue Value{} = True
isValue _       = False

isComputation :: Tm a -> Bool
isComputation Application{} = True
isComputation Case{}        = True
isComputation Handle{}      = True
isComputation Let{}         = True
isComputation Letrec{}      = True
isComputation _             = False

isUse :: Tm a -> Bool
isUse Variable{}           = True
isUse InstantiatePolyVar{} = True
isUse Command{}            = True
isUse Annotation{}         = True
isUse Application{}        = True
isUse _                    = False

isConstruction :: Tm a -> Bool
isConstruction DataConstructor{} = True
isConstruction ForeignValue{}    = True
isConstruction Lambda{}          = True
isConstruction Case{}            = True
isConstruction Handle{}          = True
isConstruction Let{}             = True
isConstruction Letrec{}          = True
isConstruction _                 = False

-- $ Binding

substitute :: Text -> Tm uid -> Tm uid -> Tm uid
substitute freev insert body = flip ycata body $ \case
  tm@(Variable v)
    | v == freev -> insert
    | otherwise -> tm
  tm -> tm

substituteAll :: HashMap Text (Tm uid) -> Tm uid -> Tm uid
substituteAll vals body = flip ycata body $ \case
  tm@(Variable v)
    | Just insert <- HashMap.lookup v vals -> insert
    | otherwise -> tm
  tm -> tm

-- WIP: something like traverseExp from
-- https://twanvl.nl/blog/haskell/traversing-syntax-trees
traverseTm
  :: Applicative f
  => (Set Text -> Tm uid -> f (Tm uid))
  -> (Set Text -> Tm uid -> f (Tm uid))
traverseTm f boundVars tm =
  let f' = f boundVars
      fWith names = f (boundVars <> Set.fromList names)
  in case tm of
       DataConstructor uid row tms -> DataConstructor uid row <$> traverse f' tms
       ForeignValue{} -> pure tm
       Lambda names body -> Lambda names <$> fWith names body
       Application appl spine -> Application <$> f' appl <*> traverse f' spine
       Case scrut branches -> do
         scrut'    <- f' scrut
         branches' <- for branches $ \(names, scope) ->
           (names,) <$> fWith names scope
         pure $ Case scrut' branches'
       Handle scrut adj peg handlers valHandler -> do
         scrut'    <- f' scrut
         handlers' <- flip (traverse.traverse) handlers $
           \(names, kName, scope) ->
             (names, kName,) <$> fWith (kName:names) scope
         vHandler' <- ($ valHandler) $ \(vName, scope) ->
           (vName,) <$> fWith [vName] scope
         pure $ Handle scrut' adj peg handlers' vHandler'
       Let body pty name scope -> do
         body'  <- f' body
         scope' <- fWith [name] scope
         pure $ Let body' pty name scope'
       Variable{} -> pure tm
       InstantiatePolyVar b args -> InstantiatePolyVar <$> f' b <*> pure args
       Command{} -> pure tm
       Annotation x ty -> Annotation <$> f' x <*> pure ty
       Letrec names defns body -> do
         defns' <- for defns $ \(pty, rhs) -> (pty,) <$> fWith names rhs
         body'  <- fWith names body
         pure $ Letrec names defns' body'
       Value val -> Value <$> f' val
       Closure names env scope -> Closure names env <$> fWith names scope
       Hole -> pure tm

-- Instance Hell:

-- IsIpld

pattern DataTyIpld uid args     = T2 "DataTy" uid args
pattern SuspendedTyIpld cty     = T1 "SuspendedTy" cty
pattern VariableTyIpld var      = T1 "VariableTy" var
pattern UidTyIpld uid           = T1 "UidTy" uid
pattern CompTyIpld dom codom    = T2 "CompTy" dom codom
pattern PegIpld ab ty           = T2 "Peg" ab ty
pattern TyArgValIpld ty         = T1 "TyArgVal" ty
pattern TyArgAbilityIpld ab     = T1 "TyArgAbility" ab
pattern AbilityIpld init uidmap = T2 "Ability" init uidmap

instance IsUid uid => IsIpld (TyFix uid) where
  toIpld = \case
    DataTy uid args     -> DataTyIpld uid args
    SuspendedTy cty     -> SuspendedTyIpld cty
    VariableTy var      -> VariableTyIpld var
    UidTy uid           -> UidTyIpld uid
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
    VariableTyIpld var      -> Just $ VariableTy var
    UidTyIpld uid           -> Just $ UidTy uid
    CompTyIpld dom codom    -> Just $ CompTy dom codom
    PegIpld ab ty           -> Just $ Peg ab ty
    TyArgValIpld ty         -> Just $ TyArgVal ty
    TyArgAbilityIpld ab     -> Just $ TyArgAbility ab
    AbilityIpld i uidmap    -> Just $ Ability i uidmap
    _                       -> Nothing

pattern CommandIpld uid row             = T2 "Command" uid row
pattern DataConstructorIpld uid row tms = T3 "DataConstructor" uid row tms
pattern ForeignValueIpld uid1 tys uid2  = T3 "ForeignValue" uid1 tys uid2
pattern LambdaIpld names body           = T2 "Lambda" names body
pattern ApplicationIpld tm spine        = T2 "Application" tm spine
pattern CaseIpld tm branches            = T2 "Case" tm branches
pattern HandleIpld tm adj peg handlers valHandler
  = T5 "Handle" tm adj peg handlers valHandler
pattern LetIpld body pty name scope     = T4 "LetIpld" body pty name scope
pattern VariableIpld name               = T1 "Variable" name
pattern InstantiatePolyVarIpld b args   = T2 "InstantiatePolyVar" b args
pattern AnnotationIpld tm ty            = T2 "Annotation" tm ty
-- pattern ValueIpld tm                    = T1 "Value" tm
pattern CutIpld cont scrutinee          = T2 "Cut" cont scrutinee
pattern LetrecIpld names defns body     = T3 "Letrec" names defns body
pattern ValueIpld val                   = T1 "Value" val
pattern ClosureIpld names env tm        = T3 "Closure" names env tm
pattern HoleIpld                        = "_Hole_"

instance IsUid uid => IsIpld (Tm uid) where
  toIpld = \case
    DataConstructor uid row tms           -> DataConstructorIpld uid row tms
    ForeignValue uid1 tys uid2            -> ForeignValueIpld uid1 tys uid2
    Lambda names body                     -> LambdaIpld names body
    Application tm spine                  -> ApplicationIpld tm spine
    Case tm branches                      -> CaseIpld tm branches
    Handle tm adj peg handlers valHandler
      -> HandleIpld tm adj peg handlers valHandler
    Let body pty name scope               -> LetIpld body pty name scope
    Variable name                         -> VariableIpld name
    InstantiatePolyVar b args             -> InstantiatePolyVarIpld b args
    Command uid row                       -> CommandIpld uid row
    Annotation tm ty                      -> AnnotationIpld tm ty
    Letrec names defns body               -> LetrecIpld names defns body
    Value val                             -> ValueIpld val
    Closure names env tm                  -> ClosureIpld names env tm
    Hole                                  -> HoleIpld
    _                                     -> error "impossible: toIpld Tm"

  fromIpld = \case
    DataConstructorIpld uid row tms -> Just $ DataConstructor uid row tms
    ForeignValueIpld uid1 tys uid2  -> Just $ ForeignValue uid1 tys uid2
    LambdaIpld names body           -> Just $ Lambda names body
    ApplicationIpld tm spine        -> Just $ Application tm spine
    CaseIpld tm branches            -> Just $ Case tm branches
    HandleIpld a b c d e            -> Just $ Handle a b c d e
    LetIpld body pty name scope     -> Just $ Let body pty name scope
    VariableIpld name               -> Just $ Variable name
    InstantiatePolyVarIpld b args   -> Just $ InstantiatePolyVar b args
    CommandIpld uid row             -> Just $ Command uid row
    AnnotationIpld tm ty            -> Just $ Annotation tm ty
    LetrecIpld names defns body     -> Just $ Letrec names defns body
    ValueIpld val                   -> Just $ Value val
    ClosureIpld names env tm        -> Just $ Closure names env tm
    HoleIpld                        -> Just $ Hole
    _                               -> Nothing

instance IsUid uid => IsIpld (Polytype uid)
instance IsUid uid => IsIpld (Adjustment uid)
instance IsUid uid => IsIpld (ConstructorDecl uid)
instance IsUid uid => IsIpld (CommandDeclaration uid)
instance IsIpld InitiateAbility
instance IsIpld Kind
instance IsIpld (DataTypeInterface Cid)
instance IsIpld (EffectInterface Cid)

