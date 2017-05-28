{-# language PatternSynonyms #-}
{-# language Rank2Types #-}
{-# language ViewPatterns #-}
module Planetary.Core.Syntax.Patterns
  ( pattern PolytypeP
  , pattern Lam
  , pattern CaseP

  -- TODO: convert to patterns?
  , handle
  , let_
  , letrec

  , pattern ForeignData
  , pattern ForeignDataTm
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

pattern ForeignData :: uid -> Value uid a b
pattern ForeignData uid = DataConstructor uid 0 []

pattern ForeignDataTm :: uid -> Tm uid a b
pattern ForeignDataTm uid = Value (ForeignData uid)

pattern DataTm :: uid -> Row -> Vector (Tm uid a b) -> Tm uid a b
pattern DataTm uid row vals = Value (DataConstructor uid row vals)

pattern V :: b -> Tm uid a b
pattern V name = Variable name

pattern CommandV :: uid -> Row -> Spine uid a b -> Tm uid a b
pattern CommandV uid row spine = Value (Command uid row spine)

pattern ConstructV :: uid -> Row -> Vector (Tm uid a b) -> Tm uid a b
pattern ConstructV uId row args = Value (DataConstructor uId row args)

pattern LambdaV :: Vector Text -> Scope Int (Tm uid a) b -> Tm uid a b
pattern LambdaV binderNames scope = Value (Lambda binderNames scope)

pattern DataConstructorV :: uid -> Row -> Vector (Tm uid a b) -> Tm uid a b
pattern DataConstructorV cid row tms = Value (DataConstructor cid row tms)

pattern VTy :: a -> ValTy uid a
pattern VTy name = VariableTy name

-- patterns
-- TODO: make these bidirectional

polytype :: Eq a => Vector (a, Kind) -> ValTy uid a -> Polytype uid a
polytype binders body =
  -- let (names, _kinds) = unzip binders
  let names = fst <$> binders
  in Polytype binders (abstract (`elemIndex` names) body)

unPolytype :: Eq a => Polytype uid a -> (Vector (a, Kind), ValTy uid a)
unPolytype (Polytype binders scope) =
  let variables = VariableTy . fst <$> binders
  in (binders, instantiate (variables !!) scope)

pattern PolytypeP :: Eq a => Vector (a, Kind) -> ValTy uid a -> Polytype uid a
pattern PolytypeP binders body <- (unPolytype -> (binders, body)) where
  PolytypeP binders body = polytype binders body

lam :: Vector Text -> Tm uid a Text -> Value uid a Text
lam vars body = Lambda vars (abstract (`elemIndex` vars) body)

unlam :: Value uid a Text -> (Vector Text, Tm uid a Text)
unlam (Lambda binderNames scope) =
  let variables = V <$> binderNames
  in (binderNames, instantiate (variables !!) scope)

pattern Lam :: Vector Text -> Tm uid a Text -> Value uid a Text
pattern Lam names tm <- (unlam -> (names, tm)) where
  Lam vars body = lam vars body

case_
  :: IsUid uid
  => uid
  -> Vector (Vector Text, Tm uid a Text)
  -> Continuation uid a Text
case_ uid tms =
  let f (vars, tm) = (vars, abstract (`elemIndex` vars) tm)
  in Case uid (f <$> tms)

uncase
  :: Continuation uid a Text
  -> (uid, Vector (Vector Text, Tm uid a Text))
uncase (Case uid tms) =
  -- let tms' = (\(vars, tm) -> (vars, let vars' = V <$> vars in instantiate (vars' !!) tm)) <$> tms
  let f (vars, tm) = (vars, let vars' = V <$> vars in instantiate (vars' !!) tm)
  in (uid, f <$> tms)

pattern CaseP
  :: IsUid uid
  => uid
  -> Vector (Vector Text, Tm uid a Text)
  -> Continuation uid a Text
pattern CaseP uid tms <- (uncase -> (uid, tms)) where
  CaseP vars body = case_ vars body

handle
  :: forall uid a b.
     Eq b
  => Adjustment uid a
  -> Peg uid a
  -> UIdMap uid (Vector (Vector b, b, Tm uid a b))
  -> (b, Tm uid a b)
  -> Continuation uid a b
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
  -> Polytype uid a
  -> Tm uid a Text
  -> Tm uid a Text
  -> Tm uid a Text
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
  -> Vector (Polytype uid a, Value uid a b)
  -> Tm uid a b
  -> Tm uid a b
letrec names binderVals body =
  Letrec binderVals (abstract (`elemIndex` names) body)
