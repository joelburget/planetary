{-# language DataKinds #-}
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
  ( closeTm
  , resolveDecls
  , resolveTm
  , ResolutionErr(..)
  ) where

import Control.Lens ((&), ix, at, (?~), (^?), (%~), _1, _2, imap)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
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

data ClosureErr
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
  in (evalState (runReaderT (runExceptT action) []) initState)

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
  -> [DeclS]
  -> Either ResolutionErr ResolvedDecls
resolveDecls initState xs =
  let ResolutionM action = nameResolutionM xs
  in (evalState (runReaderT (runExceptT action) []) initState)

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
  recTm' <- convertTm recTm
  pure (xs' & terms %~ (TermDecl name recTm':))
nameResolutionM [] = pure (ResolvedDecls mempty mempty [] [])

lookupTyVar :: Text -> ResolutionM Int
lookupTyVar var = asks (elemIndex var) >>= (?? TyVarLookup var)

lookupUid :: Text -> ResolutionM Cid
lookupUid name = gets (^? ix name) >>= (?? UnresolvedUid name)

withPushedTyVars :: [Text] -> ResolutionM a -> ResolutionM a
withPushedTyVars names = local (names ++)

withTmVars :: Vector Text -> CloseM a -> CloseM a
withTmVars names = local $ \hmap ->
      -- increment the depth
  let hmap' = hmap & (traverse . _1) %~ (+1)
      newHmap = HashMap.fromList $ flip imap names $ \i name -> (name, (0, i))
      hmap'' = HashMap.union hmap' newHmap
  in hmap''

lookupTmVar :: Text -> CloseM (Int, Int)
lookupTmVar name = asks (^? ix name) >>= (?? TmVarLookup name)

--

closeTm :: Show a => Tm a -> Either ClosureErr (Tm a)
closeTm = runCloseM . closeTm'

closeTm' :: Show a => Tm a -> CloseM (Tm a)
closeTm' = anaM $ \case
  -- bind free variables
  FreeVariable name ->
    ((\(depth, col) -> BoundVariable_ depth col) <$> lookupTmVar name) `catchError`
    (\_ -> pure $ FreeVariable_ name)

  -- binding terms
  Lambda names tm -> withTmVars names $ Lambda_ names <$> closeTm' tm
  Letrec names defns body -> withTmVars names $
    Letrec_ names <$> (traverse . _2) closeTm' defns <*> closeTm' body
  Handle adj (Peg ab codom) handlers (vName, vHandler) -> Handle_
    adj (Peg ab codom) handlers
    <$> ((vName,) <$> withTmVars [vName] (closeTm' vHandler))
  Case uid branches -> Case_ uid <$>
    traverse (\(names, branch) -> (names,) <$> (withTmVars names $ closeTm' branch)) branches
  Let pty name body -> Let_ pty name <$> withTmVars [name] (closeTm' body)

  -- non-binding terms. just handle the recursive ones
  Annotation tm ty -> Annotation_ <$> closeTm' tm <*> pure ty
  Cut l r -> Cut_ <$> closeTm' l <*> closeTm' r
  Application spine -> Application_ <$> mapM closeTm' spine
  DataConstructor uid row tms -> DataConstructor_ uid row <$> (traverse closeTm' tms)
  InstantiatePolyVar tm tyArgs -> InstantiatePolyVar_ <$> closeTm' tm <*> pure tyArgs

  other -> pure (unFix other)

convertTm :: Tm Text -> ResolutionM (Tm Cid)
convertTm = cataM $ \case
  FreeVariable_ name -> pure $ FreeVariable name
  BoundVariable_ depth column -> pure $ BoundVariable depth column
  DataConstructor_ uid row tms -> DataConstructor
    <$> lookupUid uid <*> pure row <*> pure tms
  ForeignValue_ uid1 tys uid2 -> ForeignValue
    <$> lookupUid uid1 <*> (mapM convertTy tys) <*> lookupUid uid2
  Lambda_ names tm -> pure $ Lambda names tm
  InstantiatePolyVar_ tm tyArgs
    -> InstantiatePolyVar tm <$> (mapM convertTy tyArgs)
  Command_ uid row -> Command <$> lookupUid uid <*> pure row
  Annotation_ tm ty -> Annotation tm <$> convertTy ty
  Cut_ l r -> pure $ Cut l r
  Letrec_ names defns body -> do
    defns' <- forM defns $ \(pty, tm) -> (,)
      <$> convertPolytype pty
      <*> pure tm
    pure $ Letrec names defns' body
  Application_ spine -> Application <$> mapM convertTm spine
  Case_ uid branches -> Case
    <$> lookupUid uid
    <*> pure branches
  Handle_ adj (Peg ab codom) handlers (vName, vHandler) -> Handle
    <$> convertAdjustment adj
    <*> (Peg <$> convertTy ab <*> convertTy codom)
    <*> convertUidMap handlers
    <*> ((vName,) <$> pure vHandler)
  Handle_ _ _ _ _ -> error "impossible: convertTm Handle_"
  Let_ pty name body -> Let <$> convertPolytype pty <*> pure name <*> pure body

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
  :: Unresolved EffectInterface
  -> ResolutionM (Cid, Resolved EffectInterface)
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
convertPolytype (Polytype binders scope) =
  Polytype binders <$> convertTy scope
