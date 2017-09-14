{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language TupleSections #-}
module Planetary.Support.NameResolution
  ( resolveDecls
  , resolveTm
  , ResolutionErr(..)
  ) where

import Control.Lens (cons, ix, at, _2, _3, (&), (?~), (^?), (%~))
import Control.Monad.Except
import Control.Monad.State.Strict
import Data.Functor.Fixedpoint
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
  (State ResolutionState)
  a)
  deriving ( Functor
           , Applicative
           , Monad
           , MonadError ResolutionErr
           , MonadState ResolutionState
           )

resolveTm
  :: ResolutionState
  -> Tm Text
  -> Either ResolutionErr (Tm Cid)
resolveTm initState tm =
  let ResolutionM action = resolveTm' tm
  in evalState (runExceptT action) initState

-- For each declaration:
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
  in evalState (runExceptT action) initState

nameResolutionM :: [Decl Text] -> ResolutionM ResolvedDecls
nameResolutionM (DataDecl_ (DataDecl name ddecl):xs) = do
  (cid, ddeclI) <- resolveDti ddecl
  modify (& at name ?~ cid)
  xs' <- nameResolutionM xs
  pure $ xs' & datatypes . at cid ?~ ddeclI
             & globalCids %~ cons (name, cid)
nameResolutionM (InterfaceDecl_ (InterfaceDecl name iface):xs) = do
  (cid, ifaceI) <- resolveEi iface
  modify (& at name ?~ cid)
  xs' <- nameResolutionM xs
  pure $ xs' & interfaces . at cid ?~ ifaceI
             & globalCids %~ cons (name, cid)
nameResolutionM (TermDecl_ (TermDecl name recTm):xs) = do
  xs'    <- nameResolutionM xs
  recTm' <- resolveTm' recTm
  pure $ xs' & terms %~ cons (TermDecl name recTm')
nameResolutionM [] = pure (ResolvedDecls mempty mempty [] [])

lookupUid :: Text -> ResolutionM Cid
lookupUid name = gets (^? ix name) >>= ifNotJust (UnresolvedUid name)

--

resolveTm' :: Tm Text -> ResolutionM (Tm Cid)
resolveTm' = \case
  Variable name -> pure $ Variable name
  DataConstructor uid row tms -> DataConstructor
    <$> lookupUid uid <*> pure row <*> traverse resolveTm' tms
  ForeignValue uid1 tys uid2 -> ForeignValue
    <$> lookupUid uid1 <*> mapM resolveTy tys <*> lookupUid uid2
  Lambda names tm -> Lambda names <$> resolveTm' tm
  InstantiatePolyVar tm tyArgs -> InstantiatePolyVar
    <$> resolveTm' tm
    <*> mapM resolveTy tyArgs
  Command uid row  -> Command    <$> lookupUid uid <*> pure row
  Annotation tm ty -> Annotation <$> resolveTm' tm <*> resolveTy ty
  Letrec names defns body -> do
    defns' <- forM defns $ \(pty, tm) -> (,)
      <$> resolvePolytype pty
      <*> resolveTm' tm
    body' <- resolveTm' body
    pure $ Letrec names defns' body'
  Application f s@(MixedSpine _tms _vals) -> do
    f' <- resolveTm' f
    s' <- traverse resolveTm' s
    pure $ Application f' s'
  Case tm branches -> do
    tm' <- resolveTm' tm
    branches' <- (traverse._2) resolveTm' branches
    pure $ Case tm' branches'
  Handle tm adj (Peg ab codom) handlers (vName, vHandler) -> do
    tm'       <- resolveTm' tm
    adj'      <- resolveAdjustment adj
    peg'      <- Peg <$> resolveTy ab <*> resolveTy codom
    handlers' <- resolveUidMap =<< (traverse.traverse._3) resolveTm' handlers
    vHandler' <- resolveTm' vHandler
    pure $ Handle tm' adj' peg' handlers' (vName, vHandler')
  Handle{} -> error "impossible: resolveTm' Handle"
  Let body pty name rhs -> do
    body' <- resolveTm' body
    pty'  <- resolvePolytype pty
    rhs'  <- resolveTm' rhs
    pure $ Let body' pty' name rhs'
  _ -> error "resolveTm' catchall"

resolveTy :: TyFix Text -> ResolutionM (TyFix Cid)
resolveTy = cataM $ \case
  DataTy_ uid tys        -> pure $ DataTy uid tys
  SuspendedTy_ ty        -> pure $ SuspendedTy ty
  VariableTy_ name   ->
    (UidTy <$> lookupUid name) `catchError`
    (\_ -> pure $ VariableTy name)
  UidTy_ uid             -> UidTy <$> lookupUid uid
  CompTy_ dom codom      -> pure $ CompTy dom codom
  Peg_ ab ty             -> pure $ Peg ab ty
  TyArgVal_ val          -> pure $ TyArgVal val
  TyArgAbility_ ab       -> pure $ TyArgAbility ab
  Ability_ abInit uidmap -> Ability abInit <$> resolveUidMap uidmap

resolveUidMap :: UIdMap Text [a] -> ResolutionM (UIdMap Cid [a])
resolveUidMap umap = do
  umap' <- traverse
    (\(key, tyArg) -> (,tyArg) <$> lookupUid key)
    (toList umap)
  pure (fromList umap')

resolveDti
  :: DataTypeInterface Text
  -> ResolutionM (Cid, DataTypeInterface Cid)
resolveDti (DataTypeInterface binders ctrs) = do
  ctrs' <- traverse resolveCtr ctrs
  let dti = DataTypeInterface binders ctrs'
  pure (cidOf dti, dti)

resolveEi
  :: EffectInterface Text
  -> ResolutionM (Cid, EffectInterface Cid)
resolveEi (EffectInterface binders cmds) = do
  cmds' <- traverse resolveCmd cmds
  let ei = EffectInterface binders cmds'
  pure (cidOf ei, ei)

resolveCtr
  :: ConstructorDecl Text -> ResolutionM (ConstructorDecl Cid)
resolveCtr (ConstructorDecl name args resultSaturation) = ConstructorDecl name
  <$> traverse resolveTy args
  <*> traverse resolveTy resultSaturation

resolveCmd
  :: CommandDeclaration Text
  -> ResolutionM (CommandDeclaration Cid)
resolveCmd (CommandDeclaration name dom codom) = CommandDeclaration name
  <$> traverse resolveTy dom
  <*> resolveTy codom

resolveAdjustment :: Adjustment Text -> ResolutionM (Adjustment Cid)
resolveAdjustment (Adjustment umap) = do
  umap'  <- resolveUidMap umap
  umap'' <- (traverse . traverse) resolveTy umap'
  pure $ Adjustment umap''

-- Note: this function expects its binding variables to already be pushed. See
-- `resolveTm'`
resolvePolytype :: Polytype Text -> ResolutionM (Polytype Cid)
resolvePolytype (Polytype binders scope) = Polytype binders <$> resolveTy scope
