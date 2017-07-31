{-# language ConstraintKinds #-}
{-# language DeriveDataTypeable #-}
{-# language DeriveFoldable #-}
{-# language DeriveFunctor #-}
{-# language DeriveGeneric #-}
{-# language DeriveTraversable #-}
{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language TypeFamilies #-}
module Planetary.Core.UIdMap
  ( UIdMap(..)
  , IsUid
  , fromList
  , toList
  , (<>)
  ) where

import Control.Lens (
  FunctorWithIndex(..),
  FoldableWithIndex(..),
  TraversableWithIndex(..)
  )
import Control.Lens.At (At(..), Ixed(..), IxValue, Index)
import Control.Newtype
import Data.Data
import Data.Function (on)
import Data.Hashable (Hashable)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HashMap
import Data.Monoid ((<>))
import GHC.Exts (IsList(..))
import GHC.Generics
import Network.IPLD

import Planetary.Util

type IsUid uid = (Ord uid, IsIpld uid, Hashable uid)

newtype UIdMap uid a = UIdMap (HashMap uid a)
  deriving (Eq, Show, Functor, Foldable, Traversable, Monoid, Typeable, Data,
            Generic)

instance Newtype (UIdMap uid a) (HashMap uid a) where
  pack = UIdMap
  unpack (UIdMap a) = a

type instance IxValue (UIdMap uid a) = a
type instance Index (UIdMap uid a) = uid
instance IsUid uid => At (UIdMap uid a) where
  at k f (UIdMap m) = UIdMap <$> at k f m

instance IsUid uid => Ixed (UIdMap uid a) where
  ix k f (UIdMap m) = UIdMap <$> ix k f m

instance (IsUid uid, Ord a) => Ord (UIdMap uid a) where
  compare = compare `on` toList

instance FunctorWithIndex uid (UIdMap uid)
instance FoldableWithIndex uid (UIdMap uid)

instance TraversableWithIndex uid (UIdMap uid) where
  itraverse f (UIdMap t) = UIdMap <$> HashMap.traverseWithKey f t

-- TODO: use HashMap instance when it exists
instance (IsUid uid, IsIpld a) => IsIpld (UIdMap uid a) where
  toIpld = toIpld . toList
  fromIpld = fromList <$$> fromIpld

instance IsUid uid => IsList (UIdMap uid a) where
  type Item (UIdMap uid a) = (uid, a)
  toList (UIdMap hmap) = HashMap.toList hmap
  fromList = UIdMap . HashMap.fromList
