{-# language DataKinds #-}
{-# language PatternSynonyms #-}
{-# language Rank2Types #-}
{-# language ViewPatterns #-}
-- ghc mistakenly thinks we're not using functions used in patterns
{-# options_ghc -fno-warn-unused-top-binds #-}
module Planetary.Core.Syntax.Patterns
  ( pattern AppN
  , pattern AppT
  , pattern Lam
  , pattern CaseP

  -- TODO: convert to patterns?
  , handle
  , let_
  , letrec

  , pattern FV
  , pattern BV
  , pattern VTy
  ) where

import Control.Arrow (second)
import Data.List (elemIndex)
import Data.Text (Text)

import Planetary.Core.Syntax
import Planetary.Core.UIdMap
import Planetary.Util

pattern FV :: Text -> Tm uid
pattern FV name = FreeVariable name

pattern BV :: Int -> Int -> Tm uid
pattern BV depth ix = BoundVariable depth ix

pattern VTy :: Text -> ValTy uid
pattern VTy name = FreeVariableTy name

-- patterns
-- TODO: make these bidirectional

pattern AppN :: Tm uid -> [Tm uid] -> Tm uid
pattern AppN f lst = Application f (NormalSpine lst)

pattern AppT :: Tm uid -> [Tm uid] -> Tm uid
pattern AppT f lst = Application f (TermSpine lst)

lam :: Vector Text -> Tm uid -> Tm uid
lam vars body = Lambda vars (close (`elemIndex` vars) body)

unlam :: Tm uid -> Maybe (Vector Text, Tm uid)
unlam (Lambda binderNames scope) =
  let variables = FV <$> binderNames
  in Just (binderNames, open (variables !!) scope)
unlam _ = Nothing

pattern Lam :: Vector Text -> Tm uid -> Tm uid
pattern Lam names tm <- (unlam -> Just (names, tm)) where
  Lam vars body = lam vars body

case_
  :: uid
  -> Tm uid
  -> Vector (Vector Text, Tm uid)
  -> Tm uid
case_ uid tm tms =
  let f (vars, tm') = (vars, close (`elemIndex` vars) tm')
  in Case uid tm (f <$> tms)

uncase
  :: Tm uid
  -> Maybe (uid, Tm uid, Vector (Vector Text, Tm uid))
uncase (Case uid tm tms) =
  let f (vars, tm') = (vars, let vars' = FV <$> vars in open (vars' !!) tm')
  in Just (uid, tm, f <$> tms)
uncase _ = Nothing

pattern CaseP
  :: IsUid uid
  => uid
  -> Tm uid
  -> Vector (Vector Text, Tm uid)
  -> Tm uid
pattern CaseP uid tm tms <- (uncase -> Just (uid, tm, tms)) where
  CaseP vars tm body = case_ vars tm body

handle
  :: forall uid.
     Tm uid
  -> Adjustment uid
  -> Peg uid
  -> UIdMap uid (Vector (Vector Text, Text, Tm uid))
  -> (Text, Tm uid)
  -> Tm uid
handle tm adj peg handlers (bodyVar, body) =
  let abstractor vars kVar var
        | var == kVar = Just 0
        | otherwise   = succ <$> elemIndex var vars
      handlers' = handlers <&&>
        (\(vars, kVar, rhs) -> (vars, close (abstractor vars kVar) rhs))
      body' = close1 bodyVar body
  in Handle tm adj peg handlers' (bodyVar, body')

let_
  :: Text
  -> Polytype uid
  -> Tm uid
  -> Tm uid
  -> Tm uid
let_ name pty rhs body = Let rhs pty name (close1 name body)

letrec
  :: Vector Text
  -> Vector (Polytype uid, Tm uid)
  -> Tm uid
  -> Tm uid
letrec names binderVals body = Letrec names
  ((fmap . second) (close (`elemIndex` names)) binderVals)
  (close (`elemIndex` names) body)
