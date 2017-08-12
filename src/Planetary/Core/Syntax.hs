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

import Control.Arrow (second)
import Control.Lens hiding (ix)
import qualified Control.Lens as Lens
import Control.Lens.TH (makeLenses)
import Control.Unification
import Data.Data
import qualified Data.Foldable as Foldable
import Data.Functor.Fixedpoint
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.List (find, intersperse)
import Data.Semigroup ((<>))
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import GHC.Generics
import Network.IPLD hiding (Row)
import qualified Network.IPLD as IPLD
import Data.Text.Encoding (decodeUtf8)
import Data.Text.Prettyprint.Doc

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

instance Pretty Kind where
  pretty = \case
    ValTyK -> "*"
    EffTyK -> "#"

data Ty uid ty
  -- ValTy
  = DataTy_ !ty !(Vector ty)
  | SuspendedTy_ !ty
  | BoundVariableTy_ !Int
  | FreeVariableTy_ !Text
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

instance (IsUid uid, Pretty uid) => Pretty (TyFix uid) where
  pretty = \case
    DataTy ty tys -> angles (fillSep $ pretty <$> ty : tys)
    SuspendedTy ty -> braces (pretty ty)
    BoundVariableTy i -> "BV" <+> pretty i
    FreeVariableTy t -> pretty t
    UidTy uid -> pretty uid
    CompTy args peg -> fillSep $ intersperse "->" $ pretty <$> args ++ [peg]
    Peg ab ty -> brackets (pretty ab) <+> pretty ty
    TyArgVal ty -> pretty ty
    TyArgAbility ab -> brackets (pretty ab)
    Ability init mapping ->
      let initP = case init of
            -- TODO real name
            OpenAbility -> "e"
            ClosedAbility -> "0"
          flatArgs = (\(i, r) -> pretty i <+> pretty r) <$> toList mapping
          flatArgs' = if null flatArgs then [] else "+" : flatArgs

      in fillSep $ initP : flatArgs'

instance IsUid uid => Unifiable (Ty uid) where
  zipMatch (DataTy_ uid1 args1) (DataTy_ uid2 args2) =
    if length args1 == length args2
    then Just $ DataTy_ (Right (uid1, uid2)) (Right <$> zip args1 args2)
    else Nothing
  zipMatch (SuspendedTy_ cty1) (SuspendedTy_ cty2)
    = Just (SuspendedTy_ (Right (cty1, cty2)))

  zipMatch (BoundVariableTy_ a) (BoundVariableTy_ b)
    = if a == b then Just (BoundVariableTy_ a) else Nothing

  zipMatch (FreeVariableTy_ a) (FreeVariableTy_ b)
    = if a == b then Just (FreeVariableTy_ a) else Nothing

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
pattern BoundVariableTyU v = UTerm (BoundVariableTy_ v)
pattern FreeVariableTyU v  = UTerm (FreeVariableTy_ v)
pattern UidTyU uid         = UTerm (UidTy_ uid)
pattern VariableTyU v      = UVar v

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
pattern BoundVariableTy v = Fix (BoundVariableTy_ v)
pattern FreeVariableTy v  = Fix (FreeVariableTy_ v)
pattern UidTy v           = Fix (UidTy_ v)

data Polytype uid = Polytype
  -- Universally quantify over a bunch of variables
  { polyBinders :: !(Vector (Text, Kind))
  -- resulting in a value type
  , polyVal :: !(TyFix uid)
  } deriving (Typeable, Generic)

instance (IsUid uid, Pretty uid) => Pretty (Polytype uid) where
  pretty (Polytype binders val) =
    let prettyBinder (name, kind) = case kind of
          ValTyK -> pretty name
          EffTyK -> brackets (pretty name)
        prettyBinders binders = fillSep (prettyBinder <$> binders)
    in "forall" <+> prettyBinders binders <> "." <+> pretty val

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

data TmF uid tm
  = FreeVariable_       !Text
  | BoundVariable_      !Int           !Int
  | DataConstructor_    !uid           !Row                  !(Vector tm)
  | ForeignValue_
    !uid -- ^ type id
    !(Vector (ValTy uid))
    !uid -- ^ value locator
  | Lambda_             !(Vector Text) !tm
  | InstantiatePolyVar_ !tm            !(Vector (TyArg uid))
  | Command_            !uid           !Row
  | Annotation_         !tm            !(ValTy uid)

  -- Continuation:
  --
  -- We pair each of these with 'Cut' to produce a computation. We also push
  -- these on a stack for a (call-by-push-value-esque) evaluation.
  | Application_ !tm !(Spine tm)
  | Case_ !uid !tm !(Vector (Vector Text, tm))
  | Handle_
    !tm
    !(Adjustment uid)
    !(Peg uid)
    !(UIdMap uid (Vector (Vector Text, tm)))
    !(Text, tm)
  | Let_ !tm !(Polytype uid) !Text !tm
  -- invariant: each value in a letrec is a lambda
  -- TODO: we probably want to just bind directly instead of using a lambda
  | Letrec_
    !(Vector Text)               -- ^ the name of each fn
    !(Vector (Polytype uid, tm)) -- ^ a typed lambda
    !tm                          -- ^ the body

  -- TODO: can we get rid of this in the substitution-based semantics?
  | Hole_ -- ^ Used at execution only
  deriving (Eq, Ord, Show, Typeable, Generic, Functor, Foldable, Traversable)

instance (IsUid uid, Pretty uid) => Pretty (Tm uid) where
  pretty = \case
    FreeVariable t -> pretty t
    BoundVariable depth col -> parens $ "BV" <+> pretty depth <+> pretty col
    DataConstructor uid row args -> angles $ fillSep $
      (pretty uid <> "." <> pretty row) : (pretty <$> args)
    ForeignValue ty args locator -> fillSep $
      "Foreign @" <> pretty ty : (pretty <$> args) ++ [pretty locator]
    Lambda names body ->
      "\\" <> fillSep (pretty <$> names) <+> "->" <+>
        pretty (open (FreeVariable . (names !!)) body)
    Command uid row -> pretty uid <> "." <> pretty row
    Annotation tm ty -> fillSep [pretty tm, ":", pretty ty]
    -- TODO: show the division between normalized / non-normalized
    Application tm spine -> fillSep $ pretty <$> (tm : Foldable.toList spine)
    Case uid scrutinee handlers -> vsep
      [ "case" <+> pretty scrutinee <+> "of"
      -- TODO: use align or hang?
      , indent 2 $ vsep
        [ pretty uid <> ":"
        , indent 2 $ vsep $ flip fmap handlers $ \(names, body) -> fillSep
          [ "|"
          , angles $ fillSep $ "_" : fmap pretty names
          , "->"
          , pretty $ open (FreeVariable . (names !!)) body
          ]
        ]
      ]
    Handle tm _adj peg handlers (vName, vRhs) ->
      let handlers' = prettyHandler <$> toList handlers
          prettyHandler (uid, uidHandler) = vsep
            [ pretty uid <+> colon
            , indent 2 (align $ vsep $ fmap prettyRow uidHandler)
            ]
          prettyRow (names, rhs)
            = fillSep ["|", angles (fillSep ("_" : fmap pretty names)), "->", pretty rhs]
      in vsep
           [ "Handle" <+> pretty tm <+> colon <+> pretty peg <+> "with"
           , indent 2 (align $ vsep handlers')
           , fillSep ["|", pretty vName, "->", pretty vRhs]
           ]
    Let tm ty body rhs -> fillSep
      ["let", pretty tm, ":", pretty ty, "=", pretty body, "in", pretty rhs]
    Letrec names lambdas body ->
      let rowInfo = zip names lambdas
          rows = flip fmap rowInfo $ \(name, (ty, lam)) -> vsep
            [ pretty name <+> colon <+> pretty ty
            , "=" <+> pretty lam
            ]
      in vsep
           [ "letrec"
           , indent 2 $ vsep rows
           , "in" <+> pretty body
           ]
    Hole -> "_"

instance Pretty Cid where
  pretty = pretty . decodeUtf8 . compact

pattern DataConstructor uid row tms           = Fix (DataConstructor_ uid row tms)
pattern ForeignValue uid1 rows uid2           = Fix (ForeignValue_ uid1 rows uid2)
pattern Lambda names body                     = Fix (Lambda_ names body)
pattern Application tm spine                  = Fix (Application_ tm spine)
pattern Case uid tm rows                      = Fix (Case_ uid tm rows)
pattern Handle tm adj peg handlers valHandler = Fix (Handle_ tm adj peg handlers valHandler)
pattern Let body pty name rhs                 = Fix (Let_ body pty name rhs)
pattern FreeVariable name                     = Fix (FreeVariable_ name)
pattern BoundVariable lvl ix                  = Fix (BoundVariable_ lvl ix)
pattern InstantiatePolyVar tm tyargs          = Fix (InstantiatePolyVar_ tm tyargs)
pattern Command uid row                       = Fix (Command_ uid row)
pattern Annotation tm ty                      = Fix (Annotation_ tm ty)
pattern Letrec names lambdas body             = Fix (Letrec_ names lambdas body)
pattern Hole                                  = Fix Hole_

data Spine tm = MixedSpine
  ![tm] -- ^ non-normalized terms
  ![tm] -- ^ normalized values
  deriving (Eq, Ord, Show, Typeable, Generic, Functor, Foldable, Traversable)

instance IsIpld tm => IsIpld (Spine tm)

pattern TermSpine :: [Tm uid] -> Spine (Tm uid)
pattern TermSpine tms = MixedSpine tms []

pattern NormalSpine :: [Tm uid] -> Spine (Tm uid)
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
  , _globalCids :: ![(Text, Cid)]
  , _terms      :: ![TermDecl Cid]
  } deriving Show

-- TODO: make traversals
-- namedData :: Text -> Traversal' ResolvedDecls DataTypeInterfaceI
-- namedInterface :: Text -> Traversal' ResolvedDecls EffectInterfaceI

namedData :: Text -> ResolvedDecls -> Maybe (Cid, DataTypeInterfaceI)
namedData name decls = do
  (_, cid) <- find ((== name) . fst) (_globalCids decls)
  (cid,) <$> _datatypes decls ^? Lens.ix cid

namedInterface :: Text -> ResolvedDecls -> Maybe (Cid, EffectInterfaceI)
namedInterface name decls = do
  (_, cid) <- find ((== name) . fst) (_globalCids decls)
  (cid,) <$> _interfaces decls ^? Lens.ix cid

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

-- a few common type synonyms

type CommandDeclarationI = CommandDeclaration Cid
type PolytypeI           = Polytype Cid
type ValTyI              = ValTy Cid
type TyArgI              = TyArg Cid
type DataTypeInterfaceI  = DataTypeInterface Cid
type EffectInterfaceI    = EffectInterface Cid
type TmI                 = Tm Cid

-- $ Judgements

isValue :: Tm a -> Bool
isValue BoundVariable{}      = True
isValue FreeVariable{}       = True
isValue InstantiatePolyVar{} = True
-- isValue Command{}            = True
isValue Annotation{}         = True
isValue DataConstructor{}    = True
isValue ForeignValue{}       = True
isValue Lambda{}             = True
isValue _                    = False

isComputation :: Tm a -> Bool
isComputation Command{}            = True
isComputation Letrec{}             = True
isComputation _                    = False

isUse :: Tm a -> Bool
isUse BoundVariable{}         = True
isUse FreeVariable{}          = True
isUse InstantiatePolyVar{}    = True
isUse Command{}               = True
isUse Annotation{}            = True
isUse _                       = False

isConstruction :: Tm a -> Bool
isConstruction DataConstructor{} = True
isConstruction ForeignValue{}    = True
isConstruction Lambda{}          = True
isConstruction Letrec{}          = True
isConstruction _                 = False

-- $ Binding

-- | shiftTraverse is the primitive used to implement @open@ and @close@.
--
-- We traverse the AST counting the the number of binders crossed, then call
-- the callback upon finding either a free or bound variable. @close@ is
-- implemented by converting @FreeVariable@ to @BoundVariable@ while @open@ is
-- implemented by converting @BoundVariable@ to @FreeVariable@.
shiftTraverse :: (Int -> Tm uid -> Tm uid) -> Tm uid -> Tm uid
shiftTraverse f = go 0 where

  -- This might be better expressed as a reader
  go ix v@FreeVariable{} = f ix v
  go ix v@BoundVariable{} = f ix v
  go ix (DataConstructor uid row tms) = DataConstructor uid row (go ix <$> tms)
  go _ix fv@ForeignValue{} = fv
  go ix (Lambda names scope) = Lambda names (go (succ ix) scope)
  go ix (InstantiatePolyVar tm tys) = InstantiatePolyVar (go ix tm) tys
  go _ix cmd@Command{} = cmd
  go ix (Annotation tm ty) = Annotation (go ix tm) ty
  go ix (Letrec names defns body) =
    let ix' = succ ix
    in Letrec names ((fmap . second) (go ix') defns) (go ix' body)
  go ix (Application tm spine) = Application (go ix tm) (go ix <$> spine)
  go ix (Case uid tm rows) =
    Case uid (go ix tm) ((fmap . second) (go (succ ix)) rows)
  go ix (Handle tm adj peg handlers (vName, vHandler)) =
    let handlers' = (<$$> handlers) $ second (go (succ ix))
    in Handle (go ix tm) adj peg handlers' (vName, go (succ ix) vHandler)
  go ix (Let body pty name rhs) = Let (go ix body) pty name (go (succ ix) rhs)
  go _ _ = error "impossible: shiftTraverse"

-- | Exit a scope, binding some free variables.
close :: (Text -> Maybe Int) -> Tm uid -> Tm uid
close f =
  let binder depth var = case var of
        FreeVariable name -> case f name of
          Nothing -> FreeVariable name
          Just ix -> BoundVariable depth ix
        _bv -> var
  in shiftTraverse binder

-- | Exit a scope, binding one free variable.
close1 :: Text -> Tm uid -> Tm uid
close1 name = close
  (\free -> if name == free then Just 0 else Nothing)

-- | Enter a scope, instantiating all bound variables
open :: (Int -> Tm uid) -> Tm uid -> Tm uid
open f =
  let unbinder depth var = case var of
        BoundVariable level ix -> if depth == level then f ix else var
        _fv -> var
  in shiftTraverse unbinder

-- | Enter a scope that binds one variable, instantiating it
open1 :: Tm uid -> Tm uid -> Tm uid
open1 it = open (const it)

substitute :: Text -> Tm uid -> Tm uid -> Tm uid
substitute freev insert body = flip ycata body $ \case
  tm@(FreeVariable v)
    | v == freev -> insert
    | otherwise -> tm
  tm -> tm

substituteAll :: HashMap Text (Tm uid) -> Tm uid -> Tm uid
substituteAll vals body = flip ycata body $ \case
  tm@(FreeVariable v)
    | Just insert <- HashMap.lookup v vals -> insert
    | otherwise -> tm
  tm -> tm

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

pattern T5 :: (IsIpld a, IsIpld b, IsIpld c, IsIpld d, IsIpld e) => Text -> a -> b -> c -> d -> e -> IPLD.Value
pattern T5 tag a b c d e <- (DagArray (Vx [fromIpld -> Just tag, fromIpld -> Just a, fromIpld -> Just b, fromIpld -> Just c, fromIpld -> Just d, fromIpld -> Just e])) where
  T5 tag a b c d e = DagArray (Vx [toIpld tag, toIpld a, toIpld b, toIpld c, toIpld d, toIpld e])

pattern DataTyIpld uid args     = T2 "DataTy" uid args
pattern SuspendedTyIpld cty     = T1 "SuspendedTy" cty
pattern BoundVariableTyIpld var = T1 "BoundVariableTy" var
pattern FreeVariableTyIpld var  = T1 "FreeVariableTy" var
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
    BoundVariableTy var -> BoundVariableTyIpld var
    FreeVariableTy var  -> FreeVariableTyIpld var
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
    BoundVariableTyIpld var -> Just $ SuspendedTy var
    FreeVariableTyIpld var  -> Just $ SuspendedTy var
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
pattern LambdaIpld body                 = T1 "Lambda" body
pattern ApplicationIpld tm spine        = T2 "Application" tm spine
pattern CaseIpld uid tm branches        = T3 "Case" uid tm branches
pattern HandleIpld tm adj peg handlers valHandler
  = T5 "Handle" tm adj peg handlers valHandler
pattern LetIpld body pty scope          = T3 "LetIpld" body pty scope
pattern BoundVariableIpld depth column  = T2 "BoundVariable" depth column
pattern FreeVariableIpld name           = T1 "FreeVariable" name
pattern InstantiatePolyVarIpld b args   = T2 "InstantiatePolyVar" b args
pattern AnnotationIpld tm ty            = T2 "Annotation" tm ty
-- pattern ValueIpld tm                    = T1 "Value" tm
pattern CutIpld cont scrutinee          = T2 "Cut" cont scrutinee
pattern LetrecIpld names defns body     = T3 "Letrec" names defns body

instance IsUid uid => IsIpld (Tm uid) where
  toIpld = \case
    DataConstructor uid row tms           -> DataConstructorIpld uid row tms
    ForeignValue uid1 tys uid2            -> ForeignValueIpld uid1 tys uid2
    Lambda _names body                    -> LambdaIpld body
    Application tm spine                  -> ApplicationIpld tm spine
    Case uid tm branches                  -> CaseIpld uid tm branches
    Handle tm adj peg handlers valHandler
      -> HandleIpld tm adj peg handlers valHandler
    Let body pty _name scope              -> LetIpld body pty scope
    BoundVariable depth column            -> BoundVariableIpld depth column
    FreeVariable name                     -> FreeVariableIpld name
    InstantiatePolyVar b args             -> InstantiatePolyVarIpld b args
    Command uid row                       -> CommandIpld uid row
    Annotation tm ty                      -> AnnotationIpld tm ty
    Letrec names defns body               -> LetrecIpld names defns body
    _                                     -> error "impossible: toIpld Tm"

  fromIpld = \case
    DataConstructorIpld uid row tms           -> Just $ DataConstructor uid row tms
    ForeignValueIpld uid1 tys uid2            -> Just $ ForeignValue uid1 tys uid2
    LambdaIpld body                           -> Just $ Lambda [] body
    ApplicationIpld tm spine                  -> Just $ Application tm spine
    CaseIpld uid tm branches                  -> Just $ Case uid tm branches
    HandleIpld tm adj peg handlers valHandler -> Just $
      Handle tm adj peg handlers valHandler
    LetIpld body pty scope                    -> Just $ Let body pty "" scope
    BoundVariableIpld depth column            -> Just $ BoundVariable depth column
    FreeVariableIpld name                     -> Just $ FreeVariable name
    InstantiatePolyVarIpld b args             -> Just $ InstantiatePolyVar b args
    CommandIpld uid row                       -> Just $ Command uid row
    AnnotationIpld tm ty                      -> Just $ Annotation tm ty
    LetrecIpld names defns body               -> Just $ Letrec names defns body
    _                                         -> Nothing

instance IsUid uid => IsIpld (Polytype uid)
instance IsUid uid => IsIpld (Adjustment uid)
instance IsUid uid => IsIpld (ConstructorDecl uid)
instance IsUid uid => IsIpld (CommandDeclaration uid)
instance IsIpld InitiateAbility
instance IsIpld Kind
instance IsIpld (DataTypeInterface Cid)
instance IsIpld (EffectInterface Cid)

makeLenses ''EffectInterface
makeLenses ''ResolvedDecls
makeLenses ''DataTypeInterface
