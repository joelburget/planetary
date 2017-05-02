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
module Interplanetary.UIdMap where

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

import Interplanetary.Util

type IdMap f a =
  ( Eq (f a)
  , Show (f a)
  , Functor f
  , Foldable f
  , Traversable f
  , Monoid (f a)
  , Typeable f
  , Data (f a)
  , Generic (f a)
  )

type IsUid uid = (Ord uid, Hashable uid)

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

class Unifiable f where
  -- TODO: we should give a way for solutions to escape this scope
  -- (a (mapping) state monad)
  unify :: Eq a => f a -> f a -> Maybe (f a)

instance IsUid uid => Unifiable (UIdMap uid) where
  unify (UIdMap a) (UIdMap b) = maybeIf
    (HashMap.null (HashMap.difference a b))
    (Just $ UIdMap (HashMap.union a b))

uIdMapFromList :: IsUid uid => [(uid, a)] -> UIdMap uid a
uIdMapFromList = UIdMap . HashMap.fromList

uidMapUnion :: IsUid uid => UIdMap uid a -> UIdMap uid a -> UIdMap uid a
uidMapUnion = over2 UIdMap HashMap.union

instance (IsUid uid, Ord a) => Ord (UIdMap uid a) where
  compare m1 m2 = compare (toList m1) (toList m2)

instance FunctorWithIndex uid (UIdMap uid) where
  imap = undefined
  -- TODO

instance FoldableWithIndex uid (UIdMap uid) where
  ifoldMap = undefined
  -- TODO

instance TraversableWithIndex uid (UIdMap uid) where
  -- TODO
  itraverse = undefined
  itraversed = undefined
