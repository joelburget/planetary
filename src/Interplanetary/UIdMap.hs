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

import Control.Lens (FunctorWithIndex, FoldableWithIndex, TraversableWithIndex(..))
import Control.Lens.At -- (At, Ixed, IxValue, Index)
import Control.Newtype
import Data.Data
import Data.Foldable (toList)
import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap
import GHC.Generics

import Interplanetary.UIds
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

newtype UIdMap a = UIdMap (HashMap UId a)
  deriving (Eq, Show, Functor, Foldable, Traversable, Monoid, Typeable, Data,
            Generic)

instance Newtype (UIdMap a) (HashMap UId a) where
  pack = UIdMap
  unpack (UIdMap a) = a

type instance IxValue (UIdMap a) = a
type instance Index (UIdMap a) = UId
instance At (UIdMap a) where
  at k f (UIdMap m) = UIdMap <$> at k f m

instance Ixed (UIdMap a) where
  ix k f (UIdMap m) = UIdMap <$> ix k f m

class Unifiable f where
  -- TODO: we should give a way for solutions to escape this scope
  -- (a (mapping) state monad)
  unify :: Eq a => f a -> f a -> Maybe (f a)

instance Unifiable UIdMap where
  unify (UIdMap a) (UIdMap b) = maybeIf
    (HashMap.null (HashMap.difference a b))
    (Just $ UIdMap (HashMap.union a b))

uIdMapFromList :: [(UId, a)] -> UIdMap a
uIdMapFromList = UIdMap . HashMap.fromList

uidMapUnion :: UIdMap a -> UIdMap a -> UIdMap a
uidMapUnion = over2 UIdMap HashMap.union

instance Ord a => Ord (UIdMap a) where
  compare m1 m2 = compare (toList m1) (toList m2)

instance FunctorWithIndex UId UIdMap where
  -- TODO
instance FoldableWithIndex UId UIdMap where
  -- TODO
instance TraversableWithIndex UId UIdMap where
  -- TODO
  itraverse = undefined
  itraversed = undefined

