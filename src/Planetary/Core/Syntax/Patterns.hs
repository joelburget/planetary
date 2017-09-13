{-# language DataKinds #-}
{-# language PatternSynonyms #-}
{-# language Rank2Types #-}
module Planetary.Core.Syntax.Patterns
  ( pattern AppN
  , pattern AppT

  , pattern V
  , pattern VTy
  ) where

import Data.Text (Text)

import Planetary.Core.Syntax

pattern V :: Text -> Tm uid
pattern V name = Variable name

pattern VTy :: Text -> ValTy uid
pattern VTy name = VariableTy name

-- patterns
-- TODO: make these bidirectional

pattern AppN :: Tm uid -> [Tm uid] -> Tm uid
pattern AppN f lst = Application f (NormalSpine lst)

pattern AppT :: Tm uid -> [Tm uid] -> Tm uid
pattern AppT f lst = Application f (TermSpine lst)
