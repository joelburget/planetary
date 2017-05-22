{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language LambdaCase #-}
{-# language MultiParamTypeClasses #-}
{-# language StandaloneDeriving #-}
{-# language TypeSynonymInstances #-}
module Planetary.Support.MakeTables where

import Bound (closed)
import Control.Lens ((&), ix, (.~), _1, _2, (^?))
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
-- import Data.ByteString (ByteString)
import Data.Data (Data, Typeable)
import Data.Generics.Aliases (mkM)
import Data.Generics.Schemes
import Data.List (elemIndex)
import Network.IPLD

import Planetary.Core hiding (NotClosed)
import Planetary.Util

import Debug.Trace

data TablingErr
  = UnresolvedUid String
  | VarLookup String
  | NotClosed
  deriving Show

type TablingState =
  UIdMap String (Either (DataTypeInterface Cid Int) (EffectInterface Cid Int))

newtype TablingM a = TablingM
  (ExceptT TablingErr
  (ReaderT [String]
  (State TablingState))
  a)
  deriving (Functor, Applicative, Monad, MonadError TablingErr, MonadReader [String])
deriving instance MonadState TablingState TablingM

-- For each declaration, in order:
-- * Replace any names (in the uid position) to a previously defined name with
--   the full uid
-- * Close the term and type levels (convert String free vars to Int)
-- * Generate uid, save it for future use
makeTables
  :: [Either (String, DataTypeInterface String String)
             (String, EffectInterface String String)
     ]
  -> Either TablingErr (DataTypeTable Cid Int, InterfaceTable Cid Int)
makeTables xs =
  let TablingM action = makeTablesM xs
  in evalState (runReaderT (runExceptT action) []) mempty

makeTablesM
  :: [Either (String, DataTypeInterface String String)
             (String, EffectInterface String String)
     ]
  -> TablingM (DataTypeTable Cid Int, InterfaceTable Cid Int)
makeTablesM (Left (name, ddecl):xs) = do
  (cid, ddeclI) <- convertDti ddecl
  modify (& ix name .~ Left ddeclI)
  xs' <- makeTablesM xs
  traceM "making data table"
  traceShowM xs'
  -- TODO: inconsistency with DataTypeTable not using DataTypeInterface
  -- `dataInterface` shouldn't be necessary
  pure (xs' & _1 . ix cid .~ dataInterface ddeclI)
makeTablesM (Right (name, iface):xs) = do
  (cid, ifaceI) <- convertEi iface
  modify (& ix name .~ Right ifaceI)
  xs' <- makeTablesM xs
  traceM "making interface table"
  pure (xs' & _2 . ix cid .~ ifaceI)
makeTablesM [] = pure (mempty, mempty)

lookupVar :: String -> TablingM Int
lookupVar var = do
  vars <- ask
  traceShowM vars
  elemIndex var vars ?? VarLookup var

lookupUid :: String -> TablingM Cid
lookupUid name = do
  defns <- get
  defn <- defns ^? ix name ?? UnresolvedUid name
  -- TODO: we're already calculating cids in makeTablesM -- remove duplication
  let cid = case defn of
        Left ddefn -> cidOf ddefn
        Right edefn -> cidOf edefn
  pure cid

--

convertDti
  :: DataTypeInterface String String
  -> TablingM (Cid, DataTypeInterface Cid Int)
convertDti (DataTypeInterface binders ctrs) = do
  -- let closures = imap (\i (name, _) -> (name, i)) binders
  -- ctrs' <- XXXwithpushedvars traverse convertCtr ctrs
  ctrs' <- traverse convertCtr ctrs
  let dti = DataTypeInterface [{- XXX -}] ctrs'
  pure (cidOf dti, dti)

convertEi
  :: EffectInterface String String
  -> TablingM (Cid, EffectInterface Cid Int)
convertEi (EffectInterface binders commands) = do
  commands' <- traverse convertCmd commands
  let ei = EffectInterface [{- XXX -}] commands'
  pure (cidOf ei, ei)

convertCtr :: ConstructorDecl String String -> TablingM (ConstructorDecl Cid Int)
convertCtr (ConstructorDecl vtys) = ConstructorDecl <$> traverse convertValTy vtys

convertValTy :: ValTy String String -> TablingM (ValTy Cid Int)
convertValTy = \case
  DataTy uid tyargs -> DataTy <$> lookupUid uid <*> traverse convertTyArg tyargs
  SuspendedTy cty -> SuspendedTy <$> convertCompTy cty
  VariableTy var -> VariableTy <$> lookupVar var

convertTyArg :: TyArg String String -> TablingM (TyArg Cid Int)
convertTyArg = \case
  TyArgVal valTy -> TyArgVal <$> convertValTy valTy
  TyArgAbility ability -> TyArgAbility <$> convertAbility ability

convertCompTy :: CompTy String String -> TablingM (CompTy Cid Int)
convertCompTy (CompTy dom (Peg ab codom)) = CompTy
  <$> traverse convertValTy dom
  <*> (Peg
    <$> convertAbility ab
    <*> convertValTy codom)

convertAbility :: Ability String String -> TablingM (Ability Cid Int)
convertAbility (Ability init umap) = do
  umap' <- traverse
    (\(key, tyArg) -> (,)
      <$> lookupUid key
      <*> traverse convertTyArg tyArg)
    (uIdMapToList umap)
  pure $ Ability init $ uIdMapFromList umap'

convertCmd :: CommandDeclaration String String -> TablingM (CommandDeclaration Cid Int)
convertCmd (CommandDeclaration dom codom) = CommandDeclaration
  <$> traverse convertValTy dom
  <*> convertValTy codom
