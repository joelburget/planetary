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
module Planetary.Core.UIdMap where

import Control.Lens (
  FunctorWithIndex(..),
  FoldableWithIndex(..),
  TraversableWithIndex(..)
  )
import Control.Lens.At -- (At, Ixed, IxValue, Index)
import Control.Newtype
import Data.Data
import Data.Foldable (toList)
import Data.Hashable (Hashable)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
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

instance IsUid uid => Unifiable (UIdMap uid) where
  unify (UIdMap a) (UIdMap b) = maybeIf
    (HashMap.null (HashMap.difference a b))
    (Just $ UIdMap (HashMap.union a b))

uIdMapFromList :: IsUid uid => [(uid, a)] -> UIdMap uid a
uIdMapFromList = UIdMap . HashMap.fromList

uIdMapToList :: UIdMap uid a -> [(uid, a)]
uIdMapToList (UIdMap hmap) = HashMap.toList hmap

uidMapUnion :: IsUid uid => UIdMap uid a -> UIdMap uid a -> UIdMap uid a
uidMapUnion = over2 UIdMap HashMap.union

instance (IsUid uid, Ord a) => Ord (UIdMap uid a) where
  compare m1 m2 = compare (toList m1) (toList m2)

instance FunctorWithIndex uid (UIdMap uid) where
instance FoldableWithIndex uid (UIdMap uid) where

instance TraversableWithIndex uid (UIdMap uid) where
  itraverse f (UIdMap t) = UIdMap <$> HashMap.traverseWithKey f t

-- TODO: use HashMap instance when it exists
instance (IsUid uid, IsIpld a) => IsIpld (UIdMap uid a) where
  toIpld = toIpld . uIdMapToList
  fromIpld = uIdMapFromList <$$> fromIpld
