module Tower where

open import Data.Bool
open import Data.Nat
open import Data.Vec

data Modality : Set where
  neutral : Modality
  positive : Modality
  negative : Modality
  computation : Modality

-- data Positive : Set where
--   Product : {n : Nat} -> Vec n Positive -> Positive
--
--   Sum : {n : Nat} -> n {- tag -} -> Positive -> Positive

data Negative : Set where

-- IE Commit / Delta / Edit
record Patch : Set where

-- IE Blob / Version
data Object : Set where

data Tag : Set where

-- let's introduce some judgements:
-- * typing judgement
-- * evaluation judgement

-- playing around

x : Bool
x = true ∨ false
