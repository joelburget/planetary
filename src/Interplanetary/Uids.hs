{-# options_ghc -fno-warn-missing-signatures #-}
{-# language DeriveDataTypeable #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}
{-# language TypeApplications #-}
-- Intentionally don't export any easy way to construct uids
module Interplanetary.UIds
  ( UId
  , mkUid
  , parserOnlyMakeUid
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

import Data.Binary (Binary, encode)
import Data.Byteable (toBytes)
import Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base16 as Hex
import qualified Data.ByteString.Char8 as B8
import Data.Data
import Data.Hashable (Hashable(hashWithSalt))
import Data.Word (Word8)
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

-- We need the content of the UId to be:
-- * Something we can parse into (I don't know how to parse into a `Digest`,
--   but can parse into something downstream of the digest).
-- * An instance of `Data` (not ByteString) (so we can quote it for TH)
newtype UId = UId [Word8]
  deriving (Eq, Ord, Typeable, Data, Binary)

instance Show UId where
  showsPrec d (UId w8s) = showParen (d > 10) $
    showString "UId " . showString (B8.unpack (Hex.encode (BS.pack w8s)))

instance Hashable UId where
  hashWithSalt salt (UId val) = hashWithSalt salt val

type D = Digest SHA3_256

mkUid :: Serializable a => a -> UId
mkUid = UId . BS.unpack . toBytes @D . hashlazy . encode

parserOnlyMakeUid :: ByteString -> UId
parserOnlyMakeUid = UId . BS.unpack

generateUIds :: [UId]
generateUIds = UId . BS.unpack . toBytes @D . hashFinalize <$>
  iterate (`hashUpdate` "abcd") hashInit

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
