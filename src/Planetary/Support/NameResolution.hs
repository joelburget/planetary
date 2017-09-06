{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language MultiWayIf #-}
{-# language NamedFieldPuns #-}
{-# language TypeSynonymInstances #-}
{-# language TupleSections #-}
module Planetary.Support.NameResolution
  ( closeTm
  , resolveDecls
  , resolveTm
  , ResolutionErr(..)
  ) where

import Control.Lens ((&), ix, at, (?~), (^?), (%~), _1, _2, _3, imap)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Strict
import Data.Functor.Fixedpoint
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.List (elemIndex)
import Data.Text (Text)
import Network.IPLD

import Planetary.Core hiding (NotClosed)
import Planetary.Util

data ResolutionErr
  = UnresolvedUid Text
  | TyVarLookup Text
  | NotClosed
  deriving Show

type ResolutionState = UIdMap Text Cid

newtype ResolutionM a = ResolutionM
  (ExceptT ResolutionErr
  (ReaderT [Text]
  (State ResolutionState))
  a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError ResolutionErr
           , MonadReader [Text]
           , MonadState ResolutionState
           )

newtype ClosureErr
  = TmVarLookup Text
  deriving Show

type CloseInfo = HashMap Text (Int, Int)
newtype CloseM a = CloseM (ExceptT ClosureErr (Reader CloseInfo) a)
  deriving (Functor, Applicative, Monad, MonadError ClosureErr, MonadReader CloseInfo)

runCloseM :: CloseM a -> Either ClosureErr a
runCloseM (CloseM action) = runReader (runExceptT action) HashMap.empty

resolveTm
  :: ResolutionState
  -> Tm Text
  -> Either ResolutionErr (Tm Cid)
resolveTm initState tm =
  let ResolutionM action = convertTm tm
  in evalState (runReaderT (runExceptT action) []) initState

-- For each declaration, in order:
-- * Close the term and type levels (convert Text free vars to Int)
--   (remaining free variables are okay)
-- * Replace any names (in the uid position) to a previously defined name with
--   the full uid
-- * Generate uid, save it for future use
--
-- Term conversions can spawn child type conversions (at the places where terms
-- hold types).
resolveDecls
  :: ResolutionState
  -> [Decl Text]
  -> Either ResolutionErr ResolvedDecls
resolveDecls initState xs =
  let ResolutionM action = nameResolutionM xs
  in evalState (runReaderT (runExceptT action) []) initState

nameResolutionM :: [Decl Text] -> ResolutionM ResolvedDecls
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
  recTm' <- convertTm recTm
  pure (xs' & terms %~ (TermDecl name recTm':))
nameResolutionM [] = pure (ResolvedDecls mempty mempty [] [])

lookupTyVar :: Text -> ResolutionM Int
lookupTyVar var = asks (elemIndex var) >>= ifNotJust (TyVarLookup var)

lookupUid :: Text -> ResolutionM Cid
lookupUid name = gets (^? ix name) >>= ifNotJust (UnresolvedUid name)

withPushedTyVars :: [Text] -> ResolutionM a -> ResolutionM a
withPushedTyVars names = local (names ++)

withTmVars :: Vector Text -> CloseM a -> CloseM a
withTmVars names = local $ \hmap ->
      -- increment the depth
  let hmap' = hmap & (traverse . _1) %~ succ
      newHmap = HashMap.fromList $ flip imap names $ \i name -> (name, (0, i))
      hmap'' = HashMap.union hmap' newHmap
  in hmap''

lookupTmVar :: Text -> CloseM (Int, Int)
lookupTmVar name = asks (^? ix name) >>= ifNotJust (TmVarLookup name)

--

closeTm :: Show a => Tm a -> Either ClosureErr (Tm a)
closeTm = runCloseM . closeTm'

closeTm' :: Show a => Tm a -> CloseM (Tm a)
closeTm' = \case
  -- bind free variables
  FreeVariable name ->
    (uncurry BoundVariable <$!> lookupTmVar name) `catchError`
    (\_ -> pure $! FreeVariable name)

  -- binding terms
  Lambda names tm -> withTmVars names $! Lambda names <$!> closeTm' tm
  Handle tm adj peg handlers (vName, vHandler) -> do
    tm' <- closeTm' tm
    handlers' <- handlers & (traverse . traverse)
      (\(names, kName, tm) ->
        (names, kName,) <$!> withTmVars (kName : names) (closeTm' tm))
    vHandler' <- withTmVars [vName] (closeTm' vHandler)
    pure $! Handle tm' adj peg handlers' (vName, vHandler')
  Case tm branches -> Case
    <$!> closeTm' tm
    <*> traverse
      (\(names, branch) -> (names,) <$!> withTmVars names (closeTm' branch))
      branches

  Let body pty name rhs -> do
    body' <- closeTm' body
    rhs' <- withTmVars [name] (closeTm' rhs)
    pure $! Let body' pty name rhs'

  Letrec names defns rhs -> withTmVars names $! Letrec names
    <$!> (traverse . _2) closeTm' defns
    <*> closeTm' rhs

  -- non-binding terms. just handle the recursive ones
  Annotation tm ty -> Annotation <$!> closeTm' tm <*> pure ty
  Application f spine -> Application <$!> closeTm' f <*> mapM closeTm' spine
  DataConstructor uid row tms
    -> DataConstructor uid row <$!> traverse closeTm' tms
  InstantiatePolyVar tm tyArgs
    -> InstantiatePolyVar <$!> closeTm' tm <*> pure tyArgs

  other -> pure other

convertTm :: Tm Text -> ResolutionM (Tm Cid)
convertTm = \case
  FreeVariable name -> pure $ FreeVariable name
  BoundVariable depth column -> pure $ BoundVariable depth column
  DataConstructor uid row tms -> DataConstructor
    <$> lookupUid uid <*> pure row <*> traverse convertTm tms
  ForeignValue uid1 tys uid2 -> ForeignValue
    <$> lookupUid uid1 <*> mapM convertTy tys <*> lookupUid uid2
  Lambda names tm -> Lambda names <$> convertTm tm
  InstantiatePolyVar tm tyArgs -> InstantiatePolyVar
    <$> convertTm tm
    <*> mapM convertTy tyArgs
  Command uid row -> Command <$> lookupUid uid <*> pure row
  Annotation tm ty -> Annotation <$> convertTm tm <*> convertTy ty
  Letrec names defns body -> do
    defns' <- forM defns $ \(pty@(Polytype binders _), tm) -> withPushedTyVars (fst <$> binders) $ (,)
      <$> convertPolytype pty
      <*> convertTm tm
    body' <- convertTm body
    pure $ Letrec names defns' body'
  Application f s@(MixedSpine _tms _vals) -> do
    f' <- convertTm f
    s' <- traverse convertTm s
    pure $ Application f' s'
  Case tm branches -> do
    tm' <- convertTm tm
    branches' <- (traverse._2) convertTm branches
    pure $ Case tm' branches'
  Handle tm adj (Peg ab codom) handlers (vName, vHandler) -> do
    tm' <- convertTm tm
    adj' <- convertAdjustment adj
    peg' <- Peg <$> convertTy ab <*> convertTy codom
    handlers' <- convertUidMap =<< (traverse.traverse._3) convertTm handlers
    vHandler' <- convertTm vHandler
    pure $ Handle tm' adj' peg' handlers' (vName, vHandler')
  Handle{} -> error "impossible: convertTm Handle"
  Let body pty@(Polytype binders _) name rhs -> withPushedTyVars (fst <$> binders) $ do
    body' <- convertTm body
    pty' <- convertPolytype pty
    rhs' <- convertTm rhs
    pure $ Let body' pty' name rhs'

convertTy :: TyFix Text -> ResolutionM (TyFix Cid)
convertTy = cataM $ \case
  DataTy_ uid tys        -> pure $ DataTy uid tys
  SuspendedTy_ ty        -> pure $ SuspendedTy ty
  BoundVariableTy_ i     -> pure $ BoundVariableTy i
  FreeVariableTy_ name   ->
    (UidTy <$> lookupUid name) `catchError`
    (\_ -> BoundVariableTy <$> lookupTyVar name) `catchError`
    (\_ -> pure $ FreeVariableTy name)
  UidTy_ uid             -> UidTy <$> lookupUid uid
  CompTy_ dom codom      -> pure $ CompTy dom codom
  Peg_ ab ty             -> pure $ Peg ab ty
  TyArgVal_ val          -> pure $ TyArgVal val
  TyArgAbility_ ab       -> pure $ TyArgAbility ab
  Ability_ abInit uidmap -> Ability abInit <$> convertUidMap uidmap

convertUidMap :: UIdMap Text [a] -> ResolutionM (UIdMap Cid [a])
convertUidMap umap = do
  umap' <- traverse
    (\(key, tyArg) -> (,)
      <$> lookupUid key
      <*> pure tyArg)
    (toList umap)
  pure (fromList umap')

convertDti
  :: DataTypeInterface Text
  -> ResolutionM (Cid, DataTypeInterface Cid)
convertDti (DataTypeInterface binders ctrs) = do
  let varNames = map fst binders
  ctrs' <- withPushedTyVars varNames $ traverse convertCtr ctrs
  let dti = DataTypeInterface binders ctrs'
  pure (cidOf dti, dti)

convertEi
  :: EffectInterface Text
  -> ResolutionM (Cid, EffectInterface Cid)
convertEi (EffectInterface binders cmds) = do
  let varNames = map fst binders
  cmds' <- withPushedTyVars varNames $ traverse convertCmd cmds
  let ei = EffectInterface binders cmds'
  pure (cidOf ei, ei)

convertCtr
  :: ConstructorDecl Text -> ResolutionM (ConstructorDecl Cid)
convertCtr (ConstructorDecl name args resultSaturation)
  = ConstructorDecl name
    <$> traverse convertTy args
    <*> traverse convertTy resultSaturation

convertCmd
  :: CommandDeclaration Text
  -> ResolutionM (CommandDeclaration Cid)
convertCmd (CommandDeclaration name dom codom) = CommandDeclaration name
  <$> traverse convertTy dom
  <*> convertTy codom

convertAdjustment :: Adjustment Text -> ResolutionM (Adjustment Cid)
convertAdjustment (Adjustment umap) = do
  umap' <- convertUidMap umap
  umap'' <- (traverse . traverse) convertTy umap'
  pure $ Adjustment umap''

-- Note: this function expects its binding variables to already be pushed. See
-- `convertTm`
convertPolytype :: Polytype Text -> ResolutionM (Polytype Cid)
convertPolytype (Polytype binders scope) = Polytype binders <$> convertTy scope
