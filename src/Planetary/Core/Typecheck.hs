{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language StandaloneDeriving #-}
{-# language TemplateHaskell #-}
{-# language TypeOperators #-}
{-# language TypeFamilies #-}
module Planetary.Core.Typecheck
  ( TcErr(..)
  , TypingEnv(..)
  , DataTypeTableI
  , InterfaceTableI
  , TypingEnvI
  , lfixId
  , varTypes
  , typingData
  , runTcM
  , check
  , infer
  , typingAbilities
  , typingInterfaces
  ) where

import Control.Lens hiding ((??), from, to)
import Control.Monad (forM_)
import Control.Monad.Except
import Control.Monad.Reader
import Control.Unification
import Control.Unification.IntVar
import qualified Data.Foldable as Foldable
import Data.Functor.Fixedpoint
import Data.HashMap.Strict (intersectionWith)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import Network.IPLD hiding (Row)

import Planetary.Core.Syntax
import Planetary.Core.UIdMap
import Planetary.Util

-- Limitations:
-- We (by choice) don't check kinds for now.

type UTy' = UTy IntVar

data TcErr
  = DataUIdMismatch !Cid !Cid
  | UIdMismatch
  | ApplicationSpineMismatch ![TmI] ![UTy IntVar]
  | DataSaturationMismatch ![UTy IntVar] ![UTy IntVar]
  | ConstructorArgMismatch ![TmI] ![UTy IntVar]
  | CaseMismatch ![Vector (UTy IntVar)] ![(Vector Text, Tm Cid)]
  | FailedDataTypeLookup
  | FailedConstructorLookup !Cid !Row
  | LookupCommands !Cid
  | LookupCommandTy
  | LookupVarTy !Text
  | LookupPolyVarTy !Text
  | CantInfer !TmI
  | NotClosed
  | OccursFailure !IntVar !(UTerm (Ty Cid) IntVar)
  | MismatchFailure !(Ty Cid UTy') !(Ty Cid UTy')
  | CheckFailure !String
  | LfixShape
  | NotAbility !(UTy IntVar)
  deriving Show

instance Eq TcErr where
  DataUIdMismatch c11 c12 == DataUIdMismatch c21 c22 = c11 == c21 && c12 == c22
  UIdMismatch == UIdMismatch = True
  FailedDataTypeLookup == FailedDataTypeLookup = True
  FailedConstructorLookup c1 r1 == FailedConstructorLookup c2 r2
    = c1 == c2 && r1 == r2
  LookupCommands c1 == LookupCommands c2 = c1 == c2
  LookupCommandTy == LookupCommandTy = True
  LookupVarTy a == LookupVarTy b = a == b
  LookupPolyVarTy a == LookupPolyVarTy b = a == b
  NotClosed == NotClosed = True
  CheckFailure a == CheckFailure b = a == b
  CantInfer a == CantInfer b = a == b
  LfixShape == LfixShape = True

  -- cheat on the eq instance for these since we're just using it for testing
  ApplicationSpineMismatch _ _ == ApplicationSpineMismatch _ _ = True
  DataSaturationMismatch _ _ == DataSaturationMismatch _ _ = True
  ConstructorArgMismatch _ _ == ConstructorArgMismatch _ _ = True
  CaseMismatch _ _ == CaseMismatch _ _ = True
  OccursFailure _ _ == OccursFailure _ _ = True
  MismatchFailure _ _ == MismatchFailure _ _ = True
  _a == _b = False -- TODO

-- Read-only typing information
type DataTypeTable  uid = UIdMap uid (DataTypeInterface uid)
type InterfaceTable uid = UIdMap uid (EffectInterface uid)

-- * The data type table and interface table are global and never change
-- * The ability changes as we push in and pop out of rules
data TypingEnv uid = TypingEnv
  { _typingData       :: DataTypeTable  uid
  , _typingInterfaces :: InterfaceTable uid
  , _typingAbilities  :: UTy IntVar -- :: Ability
  , _varTypes         :: Map Text (Either (UTy IntVar) PolytypeI)
  } deriving Show

makeLenses ''TypingEnv

type DataTypeTableI  = DataTypeTable  Cid
type InterfaceTableI = InterfaceTable Cid
type TypingEnvI      = TypingEnv      Cid
type TcM'            = TcM            Cid

newtype TcM uid b = TcM
  (ReaderT (TypingEnv uid)
    (ExceptT TcErr
      (IntBindingT (Ty Cid)
        Identity))
  b)
  deriving (Functor, Applicative, Monad, MonadError TcErr)
deriving instance MonadReader (TypingEnv uid) (TcM uid)

instance BindingMonad (Ty Cid) IntVar (TcM Cid) where
  lookupVar    = TcM . lift . lift . lookupVar
  freeVar      = TcM $ lift $ lift freeVar
  bindVar v tm = TcM $ lift $ lift $ bindVar v tm

instance Fallible (Ty Cid) IntVar TcErr where
  occursFailure = OccursFailure
  mismatchFailure = MismatchFailure

unify' :: UTy IntVar -> UTy IntVar -> TcM Cid ()
unify' tl tr = TcM . lift $ tl =:= tr >> return ()

-- $ Evaluation

runTcM
  :: TypingEnvI
  -> TcM' a
  -> Either TcErr a
runTcM env (TcM action) = runIdentity $
  evalIntBindingT $
  runExceptT $
  runReaderT action env

lfixId :: Cid
lfixId = mkCid "lfix"

infer :: TmI -> TcM' (UTy IntVar)
infer = \case
  -- VAR
  Variable name -> lookupVarTy name
  -- POLYVAR
  InstantiatePolyVar (Variable name) tys -> do
    Polytype binders ty' <- lookupPolyVarTy name
    boundVars <- replicateM (length binders) freeVar
    let boundVars' = Map.fromList $ zip (fst <$> binders) (boundVars)
    pure (modTm boundVars' ty')
  -- COMMAND
  Command uid row -> do
    CommandDeclaration _name from to <- lookupCommandTy uid row
    let from' = unfreeze <$> from
        to' = unfreeze to
    ambient <- getAmbient
    pure $ SuspendedTyU (CompTyU from' (PegU ambient to'))
  -- APP
  (Application f spine) -> do
    -- SuspendedTyU (CompTyU dom (PegU ability retTy)) <- infer f
    f' <- infer f
    let SuspendedTyU (CompTyU dom (PegU ability retTy)) = f'
    ambient <- getAmbient
    _ <- unify' ability ambient
    _ <- mapM_ (uncurry check)
      =<< strictZip ApplicationSpineMismatch (Foldable.toList spine) dom
    pure retTy
  -- COERCE
  Annotation n a -> do
    let a' = unfreeze a
    check n a'
    pure a'

  ForeignValue uid sat _ ->
    pure (DataTyU (UidTyU uid) (TyArgValU <$> (unfreeze <$> sat)))
  x -> throwError (CantInfer x)

check :: TmI -> UTy IntVar -> TcM' ()
-- FUN
check (Lambda binders body)
      (SuspendedTyU (CompTyU dom (PegU ability codom))) =
  -- TODO: strictZip
  let varTypes = Map.fromList $ zip binders dom
  in withValTypes' varTypes body $ \body' ->
       withAbility ability $
         check body' codom
-- DATA
check (DataConstructor uid1 row tms) (DataTyU uid2 valTysExp)
  -- Lfix extension to vanilla core frank
  --
  -- maybe this can be of help:
  -- https://www.chargueraud.org/research/2009/fixwf/fixwf.pdf
  --
  -- Example of what we're typing:
  --
  --          nilf : Listf a f
  --     ----------------------------
  --     lfix nilf : Lfix (Listf Int)
  | uid1 == lfixId = do
  _ <- unify' (UidTyU uid1) uid2
  assert LfixShape (row == 0 && length tms == 1 && length valTysExp == 1)
  let [tm] = tms
      [TyArgValU (DataTyU uid args)] = valTysExp
  v <- freeVar
  check tm (DataTyU uid (args ++ [UVar v]))

  -- Back to vanilla core frank
  | otherwise = do
  _ <- unify' (UidTyU uid1) uid2
  (argTys, valTysAct) <- lookupConstructorTy uid1 row

  mapM_ (uncurry unify') =<< strictZip DataSaturationMismatch valTysAct valTysExp
  mapM_ (uncurry check)  =<< strictZip ConstructorArgMismatch tms argTys

check (DataConstructor uid row tms) (UVar i) = do
  -- Make a variable for each subterm and solve for all of them.
  vars <- UVar <$$> replicateM (length tms) freeVar
  mapM_ (uncurry check) (zip tms vars)
  bindVar i (DataTyU (UidTyU uid) vars)

-- check (DataConstructor uid row tms) (VariableTy n) = do
--   ConstructorDecl _name argTys valTysAct <- lookupConstructorTy uid row
--   let ty = DataTy uid valTysAct
--   n =:= ty -- TODO doesn't seem like this should escape from unification
-- CASE
check (Case m rows) ty = do
  -- args :: (Vector (TyArg a))
  DataTyU (UidTyU uid) _args <- infer m

  -- extract name, args
  DataTypeInterface _binders ctrs <- lookupDataType uid
  let
      dataRows  = _constructorArgs <$> ctrs :: Vector (Vector ValTyI)
      dataRows' = unfreeze <$$> dataRows :: Vector (Vector UTy')
  zipped <- strictZip CaseMismatch dataRows' rows
  forM_ zipped $ \(dataConTys, (names, rhs)) ->
    -- TODO: strictZip
    let dataConTys' = Map.fromList $ zip names dataConTys
    in withValTypes' dataConTys' rhs (`check` ty)
-- HANDLE
check (Handle val adj peg handlers (valName, vHandler)) ty = do
  -- TODO why isn't peg checked?
  ambient <- getAmbient
  let adj' = unfreeze <$$> unAdjustment adj
  Just adjustedAmbient <- pure $ extendAbility' ambient adj'
  Just adjustedEmpty   <- pure $ extendAbility' (unfreeze emptyAbility) adj'
  valTy <- withAbility adjustedAmbient (infer val)
  cmds  <- instantiateAbility adjustedEmpty
  pairs <- uidZip handlers cmds
  forMOf_ (traverse . traverse) pairs $
    \((varNames, kName, handler), CommandDeclaration _name as b) ->
    let cTy = CompTyU [unfreeze b] (PegU ambient valTy)
        -- TODO: strictZip
        as' = zip varNames (unfreeze <$> as)
    in openAdjustmentHandler handler as' (kName, cTy) $ \tm ->
         check tm ty
  withValTypes (Map.fromList [(valName, valTy)]) $ check vHandler ty
-- LET
check (Let val pty name body) ty = do
  valTy <- instantiateWithEnv pty
  check val valTy
  withPolyty name pty $ check body ty
-- SWITCH
check m b = do
  a <- infer m
  _ <- unify' a b
  pure ()

extendAbility'
  :: UTy IntVar -> UIdMap Cid (Vector (UTy IntVar)) -> Maybe (UTy IntVar)
extendAbility' ab adj = do
  ab' <- freeze ab
  adj' <- (traverse.traverse) freeze adj
  pure $ unfreeze $ extendAbility ab' (Adjustment adj')

instantiateAbility :: UTy IntVar -> TcM' (UIdMap Cid [CommandDeclarationI])
instantiateAbility (AbilityU _ uidmap) =
  iforM uidmap $ \uid _tyArgs -> lookupCommands uid
    -- iforM cmds $ \row (CommandDeclaration as b) ->
    --   -- TODO should we be unifying the args and as? what's wrong here?
    --   todo "instantiateAbility" tyArgs as b
instantiateAbility tm = throwError (NotAbility tm)

uidZip
  :: MonadError TcErr m
  => UIdMap Cid [a]
  -> UIdMap Cid [b]
  -> m (UIdMap Cid [(a, b)])
uidZip (UIdMap as) (UIdMap bs) = UIdMap <$>
  sequence (intersectionWith (strictZip (\_ _ -> UIdMismatch)) as bs)

withValTypes :: Map Text (UTy IntVar) -> TcM' a -> TcM' a
withValTypes tys =
  let tys' = Left <$> tys
  in local (& varTypes %~ Map.union tys')

withValTypes'
  :: Map Text (UTy IntVar)
  -> Tm Cid
  -> (TmI -> TcM' a)
  -> TcM' a
withValTypes' tys scope cb = withValTypes tys (cb scope)

openAdjustmentHandler
  :: Tm Cid
  -> [(Text, UTy IntVar)]
  -> (Text, UTy IntVar)
  -> (TmI -> TcM' a)
  -> TcM' a
openAdjustmentHandler handler argTys (handlerName, handlerTy) cb = do
  let bindingTys  = Map.fromList $ Left <$$> argTys
      bindingTys' = Map.insert handlerName (Left handlerTy) bindingTys

  local (& varTypes %~ Map.union bindingTys') (cb handler)
  -- withState' envAdj (cb (open instantiator handler))

instantiateWithEnv :: PolytypeI -> TcM' (UTy IntVar)
instantiateWithEnv = todo "instantiateWithEnv"

withPolyty :: Text -> PolytypeI -> TcM' a -> TcM' a
withPolyty name pty = local (& varTypes . at name ?~ Right pty)

-- | Get the types each data constructor holds for this data type.
--
-- Question: should this be parametrized by type parameters / abilities? IE do
-- we allow GADTs?
lookupDataType :: Cid -> TcM' DataTypeInterfaceI
lookupDataType uid
  = asks (^? typingData . ix uid)
    >>= (?? FailedDataTypeLookup)

lookupConstructorTy :: Cid -> Row -> TcM' ([UTy IntVar], [UTy IntVar])
lookupConstructorTy uid row = do
  DataTypeInterface binders ctrs <- asks (^? typingData . ix uid)
    >>= (?? FailedConstructorLookup uid row)
  ConstructorDecl _name argTys valTys
    <- (ctrs ^? ix row) ?? FailedConstructorLookup uid row
  -- bind all the names in valTys
  -- boundVars <- sequence $ Map.fromList $ zip (fst <$> binders) freeVar
  boundVars <- replicateM (length binders) freeVar
  let boundVars' = Map.fromList $ zip (fst <$> binders) (boundVars)
  pure (modTm boundVars' <$> argTys, modTm boundVars' <$> valTys)

modTm :: Map Text IntVar -> TyFix' -> UTy IntVar
modTm vars = cata $ \case
  VariableTy_ name -> UVar (vars ^?! ix name)
  other -> UTerm other

lookupCommands :: Cid -> TcM' [CommandDeclarationI]
lookupCommands uid
  = asks (^? typingInterfaces . ix uid . commands)
    >>= (?? LookupCommands uid)

lookupCommandTy :: Cid -> Row -> TcM' CommandDeclarationI
lookupCommandTy uid row
  = asks (^? typingInterfaces . ix uid . commands . ix row)
    >>= (?? LookupCommandTy)

withAbility :: UTy IntVar -> TcM' b -> TcM' b
withAbility ability = local (& typingAbilities .~ ability)

getAmbient :: TcM' (UTy IntVar) -- AbilityI
getAmbient = asks (^?! typingAbilities)

lookupPolyVarTy :: Text -> TcM' PolytypeI
lookupPolyVarTy name =
  asks (^? varTypes . ix name . _Right) >>= ifNotJust (LookupPolyVarTy name)

lookupVarTy :: Text -> TcM' (UTy IntVar)
lookupVarTy name =
  asks (^? varTypes . ix name . _Left) >>= ifNotJust (LookupVarTy name)
