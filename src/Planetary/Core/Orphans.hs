{-# language FlexibleInstances #-}
{-# language UndecidableInstances #-}
{-# options_ghc -fno-warn-orphans #-}
module Planetary.Core.Orphans () where

import Bound
import Network.IPLD

import Planetary.Util

instance IsIpld b => IsIpld (Var () b)
instance IsIpld b => IsIpld (Var Int b)
instance IsIpld b => IsIpld (Var (Maybe Int) b)

instance (IsIpld b, Monad f, IsIpld (f (Var () b))) =>
  IsIpld (Scope () f b) where

  toIpld = toIpld . fromScope
  fromIpld = toScope <$$> fromIpld

instance (IsIpld b, Monad f, IsIpld (f (Var Int b))) =>
  IsIpld (Scope Int f b) where

  toIpld = toIpld . fromScope
  fromIpld = toScope <$$> fromIpld

instance (IsIpld b, Monad f, IsIpld (f (Var (Maybe Int) b))) =>
  IsIpld (Scope (Maybe Int) f b) where

  toIpld = toIpld . fromScope
  fromIpld = toScope <$$> fromIpld
