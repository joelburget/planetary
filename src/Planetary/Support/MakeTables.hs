{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language StandaloneDeriving #-}
{-# language TypeSynonymInstances #-}
module Planetary.Support.MakeTables where

import Bound (closed)
import Control.Lens ((&), ix, (.~), _1, _2)
import Control.Monad.Except
import Control.Monad.State
import Network.IPLD

import Planetary.Core hiding (NotClosed)
import Planetary.Util ((??))

data TablingErr
  = UnresolvedUid
  | NotClosed
  deriving Show

-- TODO: better naming!
type DTT = DataTypeTable Cid Int
type IT = InterfaceTable Cid Int
type DTI = DataTypeInterface Cid Int
type EI = EffectInterface Cid Int
type S = UIdMap Cid (Either DTI EI)

newtype TablingM a = TablingM
  (ExceptT TablingErr (State S) a)
  deriving (Functor, Applicative, Monad, MonadError TablingErr)
deriving instance MonadState S TablingM

-- http://stackoverflow.com/questions/5434889/is-it-possible-to-use-syb-to-transform-the-type
magic1 :: DataTypeInterface String b -> TablingM (DataTypeInterface Cid b)
magic1 dti = undefined

magic2 :: EffectInterface String b -> TablingM (EffectInterface Cid b)
magic2 = undefined

makeTables1
  :: DataTypeInterface String String
  -> TablingM (Cid, DTI)
makeTables1 ddecl = do
  ddecl' <- closed ddecl ?? NotClosed
  ddecl'' <- magic1 ddecl'
  let uid = cidOf ddecl''
  pure (uid, ddecl'')

makeTables2
  :: EffectInterface String String
  -> TablingM (Cid, EI)
makeTables2 iface = do
  iface' <- closed iface ?? NotClosed
  iface'' <- magic2 iface'
  let uid = cidOf iface''
  pure (uid, iface'')

-- For each declaration, in order:
-- * Replace any names (in the uid position) to a previously defined name with
--   the full uid
-- * Close the term and type levels (convert String free vars to Int)
-- * Generate uid, save it
makeTables
  :: [Either (DataTypeInterface String String) (EffectInterface String String)]
  -> Either TablingErr (DTT, IT)
makeTables xs =
  let TablingM action = makeTablesM xs
  in evalState (runExceptT action) mempty

makeTablesM
  :: [Either (DataTypeInterface String String) (EffectInterface String String)]
  -> TablingM (DTT, IT)
makeTablesM (Left ddecl:xs) = do
  (uid, ddeclI) <- makeTables1 ddecl
  modify (& ix uid .~ Left ddeclI)
  xs' <- makeTablesM xs
  -- TODO: inconsistency with DataTypeTable not using DataTypeInterface
  -- `dataInterface` shouldn't be necessary
  pure (xs' & _1 . ix uid .~ dataInterface ddeclI)
makeTablesM (Right iface:xs) = do
  (uid, ifaceI) <- makeTables2 iface
  modify (& ix uid .~ Right ifaceI)
  xs' <- makeTablesM xs
  pure (xs' & _2 . ix uid .~ ifaceI)
makeTablesM [] = pure (mempty, mempty)
