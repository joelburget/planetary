{-# language DataKinds #-}
{-# language GADTs #-}
{-# language PatternSynonyms #-}
{-# language Rank2Types #-}
{-# language ViewPatterns #-}
-- ghc mistakenly thinks we're not using functions used in patterns
{-# options_ghc -fno-warn-unused-top-binds #-}
module Planetary.Core.Syntax.Patterns
  ( pattern Lam
  , pattern CaseP

  -- TODO: convert to patterns?
  , handle
  , let_
  , letrec

  , pattern ForeignTm
  , pattern DataTm
  , pattern FV
  , pattern BV
  , pattern ConstructV
  , pattern LambdaV
  , pattern DataConstructorV
  , pattern VTy
  ) where

import Data.List (elemIndex)
import Data.Text (Text)

import Planetary.Core.Syntax
import Planetary.Core.UIdMap
import Planetary.Util

pattern ForeignTm :: uid -> Vector (ValTy uid) -> uid -> Tm uid
pattern ForeignTm tyUid tySat valueUid
  = Value (ForeignValue tyUid tySat valueUid)

pattern DataTm :: uid -> Row -> Vector (Tm uid) -> Tm uid
pattern DataTm uid row vals = Value (DataConstructor uid row vals)

pattern FV :: Text -> Tm uid
pattern FV name = FreeVariable name

pattern BV :: Int -> Tm uid
pattern BV ix = BoundVariable ix

pattern ConstructV :: uid -> Row -> Vector (Tm uid) -> Tm uid
pattern ConstructV uId row args = Value (DataConstructor uId row args)

pattern LambdaV :: Vector Text -> Tm uid -> Tm uid
pattern LambdaV binderNames scope = Value (Lambda binderNames scope)

pattern DataConstructorV :: uid -> Row -> Vector (Tm uid) -> Tm uid
pattern DataConstructorV cid row tms = Value (DataConstructor cid row tms)

pattern VTy :: Text -> ValTy uid
pattern VTy name = FreeVariableTy name

-- patterns
-- TODO: make these bidirectional

lam :: Vector Text -> Tm uid -> Tm uid
lam vars body = Lambda vars (abstract (`elemIndex` vars) body)

unlam :: Tm uid -> Maybe (Vector Text, Tm uid)
unlam (Lambda binderNames scope) =
  let variables = FV <$> binderNames
  in Just (binderNames, instantiate (variables !!) scope)
unlam _ = Nothing

pattern Lam :: Vector Text -> Tm uid -> Tm uid
pattern Lam names tm <- (unlam -> Just (names, tm)) where
  Lam vars body = lam vars body

case_
  :: IsUid uid
  => uid
  -> Vector (Vector Text, Tm uid)
  -> Tm uid
case_ uid tms =
  let f (vars, tm) = (vars, abstract (`elemIndex` vars) tm)
  in Case uid (f <$> tms)

uncase
  :: Tm uid
  -> Maybe (uid, Vector (Vector Text, Tm uid))
uncase (Case uid tms) =
  -- let tms' = (\(vars, tm) -> (vars, let vars' = V <$> vars in instantiate (vars' !!) tm)) <$> tms
  let f (vars, tm) = (vars, let vars' = FV <$> vars in instantiate (vars' !!) tm)
  in Just (uid, f <$> tms)
uncase _ = Nothing

pattern CaseP
  :: IsUid uid
  => uid
  -> Vector (Vector Text, Tm uid)
  -> Tm uid
pattern CaseP uid tms <- (uncase -> Just (uid, tms)) where
  CaseP vars body = case_ vars body

handle
  :: forall uid.
     Adjustment uid
  -> Peg uid
  -> UIdMap uid (Vector (Vector Text, Text, Tm uid))
  -> (Text, Tm uid)
  -> Tm uid
handle adj peg handlers (bodyVar, body) = todo "handle"
  -- let abstractor vars kVar var
  --       | var == kVar = Just Nothing
  --       | otherwise   = Just <$> elemIndex var vars
  --     handlers' = AdjustmentHandlers $
  --       (\(vars, kVar, rhs) -> abstract (abstractor vars kVar) rhs) <$$>
  --       handlers
  --     body' = abstract1 bodyVar body
  -- in Handle adj peg handlers' body'

let_
  :: Text
  -> Polytype uid
  -> Tm uid
  -> Tm uid
  -> Tm uid
let_ name pty rhs body = Cut
  -- Dragons: `rhs` and `body` are in the opposite positions of what you'd
  -- expect because body is the continuation and rhs is the term / value we're
  -- cutting against. `let_` matches the order they appear in the typical
  -- syntax.

  (Let pty name (abstract1 name body)) -- continuation
  rhs -- term

letrec
  :: Vector Text
  -> Vector (Polytype uid, Tm uid)
  -> Tm uid
  -> Tm uid
letrec names binderVals body =
  Letrec binderVals (abstract (`elemIndex` names) body)
