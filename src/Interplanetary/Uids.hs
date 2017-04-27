{-# options_ghc -fno-warn-missing-signatures #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
{-# language TypeApplications #-}
-- Intentionally don't export any easy way to construct uids
module Interplanetary.UIds
  ( UId
  , mkUid
  , intId
  , boolId
  , strId
  , intOpsId
  , boolOpsId
  , strOpsId
  , concatStrsId
  , orId
  , andId
  , unitId
  , valueTyUid
  , computationTyUid
  , pegUid
  , tyVarUid
  , tyArgUid
  , polyTyUid
  , abilityUid
  , adjustmentUid
  , tyEnvUid
  , useUid
  , constructionUid
  , spineUid
  , uidUid
  , oneUid
  , twoUid
  , fourUid
  , voidUid
  , unitUid
  , idUid
  , uidOpsId
  , uidId
  ) where

import Data.Binary (encode)
import Data.Byteable (toBytes)
import Data.Hashable (Hashable(hashWithSalt))
import Control.Distributed.Process.Serializable (Serializable)
import Crypto.Hash

-- newtype Merkle256 = Merkle256 (Crypto.Digest Crypto.SHA256)
--   deriving (Eq, Show, Ord)

-- instance Num Merkle256 where
--   fromInteger = Merkle256 . Crypto.hash . BS.pack . show

-- instance Byteable Merkle256 where
--   toBytes (Merkle256 digest) = toBytes digest

-- instance Hashable Merkle256 where
--   hashWithSalt i a = hashWithSalt i (toBytes a)

newtype UId = UId (Digest SHA3_256)
  deriving (Eq, Show, Ord) --, Hashable) -- , IsString)

instance Hashable UId where
  hashWithSalt salt (UId val) = hashWithSalt salt (toBytes val)

mkUid :: Serializable a => a -> UId
mkUid = UId . hashlazy . encode

generateUIds :: [UId]
generateUIds = UId . hashFinalize <$> iterate (`hashUpdate` "abcd") hashInit

intId
  : boolId
  : strId
  : intOpsId
  : boolOpsId
  : strOpsId
  : concatStrsId
  : orId
  : andId
  : unitId
  : valueTyUid
  : computationTyUid
  : pegUid
  : tyVarUid
  : tyArgUid
  : polyTyUid
  : abilityUid
  : adjustmentUid
  : tyEnvUid
  : useUid
  : constructionUid
  : spineUid
  : uidUid
  : voidUid
  : unitUid
  : idUid
  : uidOpsId
  : uidId
  :_ = generateUIds

oneUid, twoUid, fourUid :: UId
oneUid = mkUid @Int 1
twoUid = mkUid @Int 2
fourUid = mkUid @Int 4
