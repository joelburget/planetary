{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language MultiWayIf #-}
{-# language NamedFieldPuns #-}
{-# language StandaloneDeriving #-}
{-# language TypeSynonymInstances #-}
{-# language TupleSections #-}
module Planetary.Support.NameResolution
  (nameResolution, ResolutionErr(..))
  where

import Bound
import Control.Lens ((&), ix, at, (?~), _2, (^?), (%~), mapMOf)
import Control.Lens.Indexed (imap)
import Control.Monad.Except
import Control.Monad.Gen
import Control.Monad.Reader
import Control.Monad.State
import Data.List (elemIndex)
import Data.Text (Text)
import Data.Word (Word32)
import Network.IPLD hiding (Value)

import Planetary.Core hiding (NotClosed)
import Planetary.Util

data ResolutionErr
  = UnresolvedUid Text
  | VarLookup Text
  | NotClosed
  deriving Show

type ResolutionState = UIdMap Text Cid

-- big enough?
newtype Unique = Unique Word32
  deriving (Enum, Eq, Show)
type LevelIx = Int

type FreeV = (Unique, LevelIx)

type PartiallyConverted f = f Text Text FreeV
type FullyConverted     f = f Cid  Int  FreeV

newtype ResolutionM a = ResolutionM
  (ExceptT ResolutionErr
  (ReaderT [Text]
  (StateT ResolutionState
  (Gen Unique)))
  a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError ResolutionErr
           , MonadReader [Text]
           , MonadGen Unique
           )
deriving instance MonadState ResolutionState ResolutionM

-- For each declaration, in order:
-- * Close the term and type levels (convert Text free vars to Int)
--   (there should be no free variables!)
-- * Replace any names (in the uid position) to a previously defined name with
--   the full uid
-- * Generate uid, save it for future use
--
-- Term conversions can spawn child type conversions (at the places where terms
-- hold types).
nameResolution
  :: [DeclS]
  -> ResolutionState
  -> Either ResolutionErr ResolvedDecls
nameResolution xs initState =
  let ResolutionM action = nameResolutionM xs
  in runGen (evalStateT (runReaderT (runExceptT action) []) initState)

nameResolutionM :: [DeclS] -> ResolutionM ResolvedDecls
nameResolutionM (DataDecl_ (DataDecl name ddecl):xs) = do
  (cid, ddeclI) <- convertDti ddecl
  modify (& at name ?~ cid)
  xs' <- nameResolutionM xs
  pure $ xs' & datatypes . at cid ?~ ddeclI
             & globalCids %~ ((name, cid):)
nameResolutionM (InterfaceDecl_ (InterfaceDecl name iface):xs) = do
  (cid, ifaceI) <- convertEi iface
  modify (& at name ?~ cid)
  xs' <- nameResolutionM xs
  pure $ xs' & interfaces . at cid ?~ ifaceI
             & globalCids %~ ((name, cid):)
nameResolutionM (TermDecl_ (TermDecl name recTm):xs) = do
  xs' <- nameResolutionM xs
  Just recTm' <- pure (closed recTm)
  recTm'' <- convertTm recTm'
  Just recTm''' <- pure (closed recTm'')
  pure (xs' & terms %~ (TermDecl name recTm''':))
nameResolutionM [] = pure (ResolvedDecls mempty mempty [] [])

lookupVar :: Text -> ResolutionM Int
lookupVar var = do
  vars <- ask
  elemIndex var vars ?? VarLookup var

lookupUid :: Text -> ResolutionM Cid
lookupUid name = do
  defns <- get
  defns ^? ix name ?? UnresolvedUid name

withPushedVars :: [Text] -> ResolutionM a -> ResolutionM a
withPushedVars names = local (names ++)

--

convertDti
  :: Raw1 DataTypeInterface
  -> ResolutionM (Cid, Executable1 DataTypeInterface)
convertDti (DataTypeInterface binders ctrs) = do
  let varNames = map fst binders
      binders' = imap (\i (_, kind) -> (i, kind)) binders
  ctrs' <- withPushedVars varNames $ traverse convertCtr ctrs
  let dti = DataTypeInterface binders' ctrs'
  pure (cidOf dti, dti)

convertEi
  :: Raw1 EffectInterface
  -> ResolutionM (Cid, Executable1 EffectInterface)
convertEi (EffectInterface binders cmds) = do
  let varNames = map fst binders
      binders' = imap (\i (_, kind) -> (i, kind)) binders
  cmds' <- withPushedVars varNames $ traverse convertCmd cmds
  let ei = EffectInterface binders' cmds'
  pure (cidOf ei, ei)

convertCtr
  :: Raw1 ConstructorDecl -> ResolutionM (Executable1 ConstructorDecl)
convertCtr (ConstructorDecl name vtys)
  = ConstructorDecl name <$> traverse convertValTy vtys

convertValTy :: Raw1 ValTy -> ResolutionM (Executable1 ValTy)
convertValTy = \case
  DataTy uid tyargs -> DataTy
    <$> lookupUid uid
    <*> traverse convertTyArg tyargs
  SuspendedTy cty   -> SuspendedTy <$> convertCompTy cty
  VariableTy var    -> VariableTy  <$> lookupVar var

convertTyArg :: Raw1 TyArg -> ResolutionM (Executable1 TyArg)
convertTyArg = \case
  TyArgVal valTy -> TyArgVal <$> convertValTy valTy
  TyArgAbility ability -> TyArgAbility <$> convertAbility ability

convertCompTy :: Raw1 CompTy -> ResolutionM (Executable1 CompTy)
convertCompTy (CompTy dom (Peg ab codom)) = CompTy
  <$> traverse convertValTy dom
  <*> (Peg
    <$> convertAbility ab
    <*> convertValTy codom)

convertAbility :: Raw1 Ability -> ResolutionM (Executable1 Ability)
convertAbility (Ability initAb umap)
  = Ability initAb <$> convertUidMap convertTyArg umap

convertCmd
  :: Raw1 CommandDeclaration
  -> ResolutionM (Executable1 CommandDeclaration)
convertCmd (CommandDeclaration dom codom) = CommandDeclaration
  <$> traverse convertValTy dom
  <*> convertValTy codom

convertTm :: PartiallyConverted Tm -> ResolutionM (FullyConverted Tm)
convertTm = \case
  Variable v -> pure (Variable v)
  InstantiatePolyVar tyVar tyArgs -> InstantiatePolyVar tyVar
    <$> mapM convertTyArg tyArgs
  Annotation val valTy -> Annotation
    <$> convertValue val
    <*> convertValTy valTy
  Value val -> Value <$> convertValue val
  Cut { cont, scrutinee } -> Cut <$> convertContinuation cont <*> convertTm scrutinee
  Letrec defns body ->
        -- we have to be careful here -- the variables the polytype binds also
        -- scope over the term
    let convertPolyty (pty, val) = do
          let names = case pty of
                Polytype binders _body -> fst <$> binders
          pty' <- withPushedVars names (convertPolytype pty)
          val' <- withPushedVars names (convertValue val)
          pure (pty', val')
    in Letrec <$> mapM convertPolyty defns <*> convertIntScope body

convertValue :: PartiallyConverted Value -> ResolutionM (FullyConverted Value)
convertValue = \case
  Command cid row -> Command
    <$> lookupUid cid
    <*> pure row
  DataConstructor cid row spine -> DataConstructor
    <$> lookupUid cid
    <*> pure row
    <*> mapM convertTm spine
  Lambda binderName scope -> Lambda binderName <$> convertIntScope scope

convertAdjustment :: Adjustment' -> ResolutionM AdjustmentI
convertAdjustment (Adjustment umap)
  = Adjustment <$> convertUidMap convertTyArg umap

convertUidMap
  :: (a -> ResolutionM b) -> UIdMap Text [a] -> ResolutionM (UIdMap Cid [b])
convertUidMap f umap = do
  umap' <- traverse
    (\(key, tyArg) -> (,)
      <$> lookupUid key
      <*> traverse f tyArg)
    (uIdMapToList umap)
  pure (uIdMapFromList umap')

convertHandlers
  :: PartiallyConverted AdjustmentHandlers
  -> ResolutionM (FullyConverted AdjustmentHandlers)
convertHandlers (AdjustmentHandlers handlers) =
  AdjustmentHandlers <$> convertUidMap convertMaybeScope handlers

-- Note: this function expects its binding variables to already be pushed. See
-- `convertTm`
convertPolytype :: Polytype' -> ResolutionM PolytypeI
convertPolytype (Polytype binders scope) = do
  let newBinders = imap (,) (snd <$> binders)
      names = fst <$> binders
      ty = instantiate (VariableTy . (names !!)) scope
  convertedTy <- convertValTy ty
  pure $ Polytype newBinders (abstract Just convertedTy)

convertContinuation
  :: PartiallyConverted Continuation
  -> ResolutionM (FullyConverted Continuation)
convertContinuation = \case
  Application spine -> Application <$> mapM convertTm spine
  Case cid handlers -> Case
    <$> lookupUid cid
    <*> mapMOf (traverse._2) convertIntScope handlers
  Handle adj (Peg ab codom) handlers scope -> Handle
    <$> convertAdjustment adj
    <*> (Peg <$> convertAbility ab <*> convertValTy codom)
    <*> convertHandlers handlers
    <*> convertUnitScope scope
  Let polyty name scope ->
    Let <$> convertPolytype polyty <*> pure name <*> convertUnitScope scope

convertMaybeScope
  :: Scope (Maybe Int) (Tm Text Text) FreeV
  -> ResolutionM (Scope (Maybe Int) (Tm Cid Int) FreeV)
convertMaybeScope scope = do
  unique <- gen
  let makeFree = Variable . (unique,) . \case
        Nothing -> 0
        Just i  -> succ i
      tm = instantiate makeFree scope
  convertedTm <- convertTm tm
  let closer (unique', i) = if
        | unique' /= unique -> Nothing
        | i == 0            -> Just Nothing
        | otherwise         -> Just (Just (pred i))
  pure (abstract closer convertedTm)

convertIntScope
  :: Scope Int (Tm Text Text) FreeV
  -> ResolutionM (Scope Int (Tm Cid Int) FreeV)
convertIntScope scope = do
  unique <- gen
  let tm = instantiate (Variable . (unique,)) scope
  convertedTm <- convertTm tm
  let closer (unique', i) = if
        | unique' /= unique -> Nothing
        | otherwise         -> Just i
  pure (abstract closer convertedTm)

convertUnitScope
  :: Scope () (Tm Text Text) FreeV
  -> ResolutionM (Scope () (Tm Cid Int) FreeV)
convertUnitScope scope = do
  unique <- gen
  let free = Variable (unique, 0)
      tm = instantiate1 free scope
  convertedTm <- convertTm tm
  pure (abstract1 (unique, 0) convertedTm)
