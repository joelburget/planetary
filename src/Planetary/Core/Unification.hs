{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language StandaloneDeriving #-}
{-# language ViewPatterns #-}
module Planetary.Core.Unification
  ( HasUnification(..)
  , UnificationError(..)
  , unifyValTys
  , unifyAbilities
  , unifyTyArgs
  , (=:)
  ) where

import Control.Monad.State.Strict
import qualified Data.HashMap.Lazy as HashMap

import Planetary.Util
import Planetary.Core.Syntax
import Planetary.Core.UIdMap

data UnificationError
  = OccursFailure Int ValTyI
  | DataTyUnification ValTyI ValTyI
  | AbilityUnification AbilityI AbilityI
  | ValTyLength (Vector ValTyI) (Vector ValTyI)
  | TyArgUnification TyArgI TyArgI
  | TyArgLength (Vector TyArgI) (Vector TyArgI)
  | UnimplementedEffectUnification PolytypeI
  | UnspecifiedFailure
  deriving (Eq, Show)

class Monad m => HasUnification m where
  cantUnify :: UnificationError -> m a
  locally :: m a -> m a
  lookupVar :: Int -> m (Maybe ValTyI)
  bindVar :: Int -> ValTyI -> m ()
  seenAs :: Int -> ValTyI -> m ()

  -- TODO: should we have `freshVar`?

(=:) :: HasUnification m => Int -> ValTyI -> m ()
{-# INLINE (=:) #-}
(=:) = bindVar

unifyAbilities ::
  HasUnification m => AbilityI -> AbilityI -> m AbilityI
unifyAbilities
  ab1@(Ability init1 (UIdMap tyArgs1))
  ab2@(Ability init2 (UIdMap tyArgs2)) = do
  let leftOnly  = HashMap.difference tyArgs1 tyArgs2
      rightOnly = HashMap.difference tyArgs2 tyArgs1

  boths <- sequence $ HashMap.intersectionWith unifyTyArgVec tyArgs1 tyArgs2

  let mergedTyArgs = UIdMap $ HashMap.unions [leftOnly, rightOnly, boths]

  case (init1, init2) of
    (OpenAbility, OpenAbility) -> pure $ Ability OpenAbility mergedTyArgs
    (OpenAbility, ClosedAbility) ->
      if HashMap.null leftOnly
      then pure $ Ability ClosedAbility (UIdMap tyArgs1)
      else cantUnify (AbilityUnification ab1 ab2)
    (ClosedAbility, OpenAbility) ->
      if HashMap.null rightOnly
      then pure $ Ability ClosedAbility (UIdMap tyArgs2)
      else cantUnify (AbilityUnification ab1 ab2)
    (ClosedAbility, ClosedAbility) ->
      if tyArgs1 == tyArgs2
      then pure $ Ability ClosedAbility (UIdMap tyArgs1)
      else cantUnify (AbilityUnification ab1 ab2)

unifyPegs ::
  HasUnification m => PegI -> PegI -> m PegI
unifyPegs (Peg ab1 val1) (Peg ab2 val2) = do
  Peg <$> unifyAbilities ab1 ab2 <*> unifyValTys val1 val2

unifyCompTys :: HasUnification m => CompTyI -> CompTyI -> m CompTyI
unifyCompTys (CompTy dom1 codom1) (CompTy dom2 codom2) = CompTy
  <$> unifyValTyVec dom1 dom2
  <*> unifyPegs codom1 codom2

unifyValTyVec
  :: HasUnification m => Vector ValTyI -> Vector ValTyI -> m (Vector ValTyI)
unifyValTyVec vals1 vals2 =
  if length vals1 == length vals2
  then zipWithM unifyValTys vals1 vals2
  else cantUnify (ValTyLength vals1 vals2)

unifyTyArgs :: HasUnification m => TyArgI -> TyArgI -> m TyArgI
unifyTyArgs (TyArgVal v1) (TyArgVal v2) = TyArgVal <$> unifyValTys v1 v2
unifyTyArgs (TyArgAbility a1) (TyArgAbility a2)
  = TyArgAbility <$> unifyAbilities a1 a2
unifyTyArgs arg1 arg2 = cantUnify (TyArgUnification arg1 arg2)

unifyTyArgVec
  :: HasUnification m => Vector TyArgI
  -> Vector TyArgI
  -> m (Vector TyArgI)
unifyTyArgVec args1 args2 =
  if length args1 == length args2
  then zipWithM unifyTyArgs args1 args2
  else cantUnify (TyArgLength args1 args2)

-- N.B., this assumes there are no directly-cyclic chains!
--
-- | Canonicalize a chain of variables so they all point directly
-- to the last variable in the chain, regardless of whether it is
-- bound or not. This allows detecting many cases where multiple
-- variables point to the same term, thereby allowing us to avoid
-- re-unifying the term they point to.
semiprune :: HasUnification m => ValTyI -> m ValTyI
semiprune t0@(VariableTy v0) = loop t0 v0
    where
    -- We pass the @t@ for @v@ in order to add just a little more sharing.
    loop t0' v0' = do
        mb <- lookupVar v0'
        case mb of
            Nothing -> return t0'
            Just t  -> case t of
              VariableTy  v  -> do
                  finalVar <- loop t v
                  v0' =: finalVar
                  return finalVar
              _  -> return t0'
semiprune t0 = return t0

-- TODO: verify correctness, especially for the visited-set stuff.
-- TODO: return Maybe(UTerm t v) in the loop so we can avoid updating bindings trivially
-- TODO: figure out why unifyOccurs is so much faster on pure ground terms!! The only difference there is in lifting over StateT...
--
-- | Unify two terms, or throw an error with an explanation of why
-- unification failed. Since bindings are stored in the monad, the
-- two input terms and the output term are all equivalent if
-- unification succeeds. However, the returned value makes use of
-- aggressive opportunistic observable sharing, so it will be more
-- efficient to use it in future calculations than either argument.
-- unify :: ValTyI -> ValTyI -> Either UnificationError ValTyI
-- unify tl0 tr0 = evalStateT (unUnify $ unifyLoop tl0 tr0) IntMap.empty

unifyValTys :: HasUnification m => ValTyI -> ValTyI -> m ValTyI
unifyValTys d1@(DataTy uid1 args1) d2@(DataTy uId2 args2) =
  if uid1 == uId2
  then DataTy uid1 <$> unifyTyArgVec args1 args2
  else cantUnify (DataTyUnification d1 d2)
unifyValTys (SuspendedTy cty1) (SuspendedTy cty2)
  = SuspendedTy <$> unifyCompTys cty1 cty2
unifyValTys a b = unifyLoop a b -- TODO: is this right?

unifyLoop :: HasUnification m => ValTyI -> ValTyI -> m ValTyI
unifyLoop tl0' tr0' = do
    tl0 <- semiprune tl0'
    tr0 <- semiprune tr0'
    case (tl0, tr0) of
        (VariableTy vl, VariableTy vr)
            | vl == vr  -> return tr0
            | otherwise -> do
                mtl <- lookupVar vl
                mtr <- lookupVar vr
                case (mtl, mtr) of
                    (Nothing, Nothing) -> do vl =: tr0 ; return tr0
                    (Nothing, Just _ ) -> do vl =: tr0 ; return tr0
                    (Just _ , Nothing) -> do vr =: tl0 ; return tl0
                    (Just tl, Just tr) -> do
                        t <- locally $ do
                            vl `seenAs` tl
                            vr `seenAs` tr
                            unifyValTys tl tr
                        vr =: t
                        vl =: tr0
                        return tr0

        (VariableTy vl, _) -> do
            t <- do
                mtl <- lookupVar vl
                case mtl of
                    Nothing         -> return tr0
                    Just tl -> locally $ do
                        vl `seenAs` tl
                        unifyValTys tl tr0
            vl =: t
            return tl0

        (_, VariableTy vr) -> do
            t <- do
                mtr <- lookupVar vr
                case mtr of
                    Nothing         -> return tl0
                    Just tr -> locally $ do
                        vr `seenAs` tr
                        unifyValTys tl0 tr
            vr =: t
            return tr0

        (_, __) -> unifyValTys tl0 tr0

_impossible_unify :: String
{-# NOINLINE _impossible_unify #-}
_impossible_unify = "unify: the impossible happened"
