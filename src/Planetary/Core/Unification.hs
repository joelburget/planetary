{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
module Planetary.Core.Unification
  ( HasUnification(..)
  , UnificationError(..)
  , unify
  , (=:)
  ) where

import Control.Monad.State.Strict
import qualified Data.HashMap.Lazy as HashMap
import Network.IPLD (Cid)

import Planetary.Util
import Planetary.Core.Syntax
import Planetary.Core.UIdMap

data UnificationError
  = OccursFailure Int ValTyI
  | DataTyUnification ValTyI ValTyI
  | AbilityUnification AbilityI AbilityI
  | ValTyLength (Vector ValTyI) (Vector ValTyI)
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

unify
  :: HasUnification m => Ty tag Cid Int -> Ty tag Cid Int -> m (Ty tag Cid Int)
unify a@VariableTy{} b = unifyLoop a b
unify a b@VariableTy{} = unifyLoop a b
unify
  ab1@(Ability init1 (UIdMap tyArgs1))
  ab2@(Ability init2 (UIdMap tyArgs2)) = do
  let leftOnly  = HashMap.difference tyArgs1 tyArgs2
      rightOnly = HashMap.difference tyArgs2 tyArgs1

  boths <- sequence $ HashMap.intersectionWith unifyTyArgVec tyArgs1 tyArgs2

  let mergedTyArgs = UIdMap $ HashMap.unions [leftOnly, rightOnly, boths]
      failure = cantUnify (AbilityUnification ab1 ab2)
      leftOnly'  = pure $ Ability ClosedAbility (UIdMap tyArgs1)
      rightOnly' = pure $ Ability ClosedAbility (UIdMap tyArgs2)

  case (init1, init2) of
    (OpenAbility, OpenAbility) -> pure $ Ability OpenAbility mergedTyArgs
    (OpenAbility, ClosedAbility) ->
      if HashMap.null leftOnly then leftOnly' else failure
    (ClosedAbility, OpenAbility) ->
      if HashMap.null rightOnly then rightOnly' else failure
    (ClosedAbility, ClosedAbility) ->
      if tyArgs1 == tyArgs2 then leftOnly' else failure

unify d1@(DataTy uid1 args1) d2@(DataTy uId2 args2) =
  if uid1 == uId2
  then DataTy uid1 <$> unifyTyArgVec args1 args2
  else cantUnify (DataTyUnification d1 d2)
unify (SuspendedTy cty1) (SuspendedTy cty2) = SuspendedTy <$> unify cty1 cty2

unify (Peg ab1 val1) (Peg ab2 val2) = Peg <$> unify ab1 ab2 <*> unify val1 val2

unify (CompTy dom1 codom1) (CompTy dom2 codom2) = CompTy
  <$> unifyValTyVec dom1 dom2
  <*> unify codom1 codom2

unify (TyArgVal v1) (TyArgVal v2)         = TyArgVal <$> unify v1 v2
unify (TyArgAbility a1) (TyArgAbility a2) = TyArgAbility <$> unify a1 a2
unify ty1 ty2                             = cantUnify UnspecifiedFailure

unifyValTyVec
  :: HasUnification m => Vector ValTyI -> Vector ValTyI -> m (Vector ValTyI)
unifyValTyVec vals1 vals2 =
  if length vals1 == length vals2
  then zipWithM unify vals1 vals2
  else cantUnify (ValTyLength vals1 vals2)

unifyTyArgVec
  :: HasUnification m => Vector TyArgI
  -> Vector TyArgI
  -> m (Vector TyArgI)
unifyTyArgVec args1 args2 =
  if length args1 == length args2
  then zipWithM unify args1 args2
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
                            unify tl tr
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
                        unify tl tr0
            vl =: t
            return tl0

        (_, VariableTy vr) -> do
            t <- do
                mtr <- lookupVar vr
                case mtr of
                    Nothing         -> return tl0
                    Just tr -> locally $ do
                        vr `seenAs` tr
                        unify tl0 tr
            vr =: t
            return tr0

        (_, __) -> unify tl0 tr0
