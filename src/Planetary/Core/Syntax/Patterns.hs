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
  , pattern V
  , pattern CommandV
  , pattern ConstructV
  , pattern LambdaV
  , pattern DataConstructorV
  , pattern VTy
  ) where

import Bound
import Data.List (elemIndex)
import Data.Text (Text)

import Planetary.Core.Syntax
import Planetary.Core.UIdMap
import Planetary.Util

pattern ForeignTm :: uid -> Vector (ValTy uid) -> uid -> Tm 'TM uid b
pattern ForeignTm tyUid tySat valueUid
  = Value (ForeignValue tyUid tySat valueUid)

pattern DataTm :: uid -> Row -> Vector (Tm 'TM uid b) -> Tm 'TM uid b
pattern DataTm uid row vals = Value (DataConstructor uid row vals)

pattern V :: b -> Tm 'TM uid b
pattern V name = Variable name

pattern CommandV :: uid -> Row -> Tm 'TM uid b
pattern CommandV uid row = Value (Command uid row )

pattern ConstructV :: uid -> Row -> Vector (Tm 'TM uid b) -> Tm 'TM uid b
pattern ConstructV uId row args = Value (DataConstructor uId row args)

pattern LambdaV :: Vector Text -> Scope Int (Tm 'TM uid ) b -> Tm 'TM uid b
pattern LambdaV binderNames scope = Value (Lambda binderNames scope)

pattern DataConstructorV :: uid -> Row -> Vector (Tm 'TM uid b) -> Tm 'TM uid b
pattern DataConstructorV cid row tms = Value (DataConstructor cid row tms)

pattern VTy :: Text -> ValTy uid
pattern VTy name = FreeVariableTy name

-- patterns
-- TODO: make these bidirectional

lam :: Vector Text -> Tm 'TM uid Text -> Tm 'VALUE uid Text
lam vars body = Lambda vars (abstract (`elemIndex` vars) body)

unlam :: Tm 'VALUE uid Text -> Maybe (Vector Text, Tm 'TM uid Text)
unlam (Lambda binderNames scope) =
  let variables = V <$> binderNames
  in Just (binderNames, instantiate (variables !!) scope)
unlam _ = Nothing

pattern Lam :: Vector Text -> Tm 'TM uid Text -> Tm 'VALUE uid Text
pattern Lam names tm <- (unlam -> Just (names, tm)) where
  Lam vars body = lam vars body

case_
  :: IsUid uid
  => uid
  -> Vector (Vector Text, Tm 'TM uid Text)
  -> Tm 'CONTINUATION uid Text
case_ uid tms =
  let f (vars, tm) = (vars, abstract (`elemIndex` vars) tm)
  in Case uid (f <$> tms)

uncase
  :: Tm 'CONTINUATION uid Text
  -> Maybe (uid, Vector (Vector Text, Tm 'TM uid Text))
uncase (Case uid tms) =
  -- let tms' = (\(vars, tm) -> (vars, let vars' = V <$> vars in instantiate (vars' !!) tm)) <$> tms
  let f (vars, tm) = (vars, let vars' = V <$> vars in instantiate (vars' !!) tm)
  in Just (uid, f <$> tms)
uncase _ = Nothing

pattern CaseP
  :: IsUid uid
  => uid
  -> Vector (Vector Text, Tm 'TM uid Text)
  -> Tm 'CONTINUATION uid Text
pattern CaseP uid tms <- (uncase -> Just (uid, tms)) where
  CaseP vars body = case_ vars body

handle
  :: forall uid b.
     Eq b
  => Adjustment uid
  -> Peg uid
  -> UIdMap uid (Vector (Vector b, b, Tm 'TM uid b))
  -> (b, Tm 'TM uid b)
  -> Tm 'CONTINUATION uid b
handle adj peg handlers (bodyVar, body) =
  let abstractor vars kVar var
        | var == kVar = Just Nothing
        | otherwise   = Just <$> elemIndex var vars
      handlers' = AdjustmentHandlers $
        (\(vars, kVar, rhs) -> abstract (abstractor vars kVar) rhs) <$$>
        handlers
      body' = abstract1 bodyVar body
  in Handle adj peg handlers' body'

let_
  :: Text
  -> Polytype uid
  -> Tm 'TM uid Text
  -> Tm 'TM uid Text
  -> Tm 'TM uid Text
let_ name pty rhs body = Cut
  -- Dragons: `rhs` and `body` are in the opposite positions of what you'd
  -- expect because body is the continuation and rhs is the term / value we're
  -- cutting against. `let_` matches the order they appear in the typical
  -- syntax.

  (Let pty name (abstract1 name body)) -- continuation
  rhs -- term

letrec
  :: Eq b
  => Vector b
  -> Vector (Polytype uid, Tm 'VALUE uid b)
  -> Tm 'TM uid b
  -> Tm 'TM uid b
letrec names binderVals body =
  Letrec binderVals (abstract (`elemIndex` names) body)
