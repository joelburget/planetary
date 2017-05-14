{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
module Interplanetary.Meta where

-- import qualified Data.ByteString as B
-- import Data.Text (Text)
-- import qualified Data.Vector as V
-- import Data.Vector (Vector)
-- import Data.Word (Word32)

import Interplanetary.Syntax
import Interplanetary.Util

-- pattern V2 :: a -> a -> Vector a
-- pattern V2 a b <- (V.toList -> [a, b]) where
--   V2 a b = V.fromList [a, b]

-- pattern Vx :: [a] -> Vector a
-- pattern Vx lst <- (V.toList -> lst) where
--   Vx lst = V.fromList lst

-- | Transform an expression into the representation of that epxression
--
-- When do you actually need this in the genesis language? Well, our goal is to
-- *enhance* the language, not create new ones from scratch. Indicating we want
-- to borrow from the base language.
--
-- `splice . quote` of course results in the original term.
quote :: TmI -> TmI
quote = todo "quote"

-- | Transfer the representation of a term to a term
splice :: TmI -> TmI
splice = todo "splice"

-- merkleEff :: TmI -> TmI
-- merkleEff = todo "merkleEff"

-- joinHash :: Merkle256 -> Merkle256 -> Merkle256
-- joinHash a b = hash (B.append (toBytes a) (toBytes b))

-- class Merkle a where
--   merkle :: a -> Merkle256

-- instance Merkle ValueI where
-- instance Merkle ContinuationI where

-- instance Merkle TmI where
--   merkle = \case
--     Variable b -> hash "Variable" `joinHash` (B.pack (show b))
--     InstantiatePolyVar b args -> todo "Merkle TmI"
