{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language LambdaCase #-}
module Interplanetary.Meta where

import Data.Text (Text)
import qualified Data.Vector as V
import Data.Vector (Vector)
import Data.Word (Word32)

import Interplanetary.Genesis

pattern V2 :: a -> a -> Vector a
pattern V2 a b <- (V.toList -> [a, b]) where
  V2 a b = V.fromList [a, b]

pattern Vx :: [a] -> Vector a
pattern Vx lst <- (V.toList -> lst) where
  Vx lst = V.fromList lst

pattern ValueBindRep :: Binder ann -> HeapVal ann
pattern ValueBindRep binder <- HeapTagged 0 ann

pattern TypeBindRep :: Binder ann -> HeapVal ann
pattern TypeBindRep binder = HeapTagged 1 (HeapMultiVal [])

-- | Transfor an expression into the representation of that epxression
--
-- When do you actually need this in the genesis language? Well, our goal is to
-- *enhance* the language, not create new ones from scratch. Indicating we want
-- to borrow from the base language.
--
-- `splice . quote` of course results in the original term.
quote :: Term ann -> Term ann
quote = todo "quote"

-- | Transfer the representation of a term to a term
splice :: Term ann -> Term ann
splice = todo "splice"
