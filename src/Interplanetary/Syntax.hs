{-# language LambdaCase #-}
{-# language GADTs #-}
{-# language KindSignatures #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language DataKinds #-}
{-# language TupleSections #-}
{-# language PatternSynonyms #-}
{-# language Rank2Types #-}
module Interplanetary.Syntax where

import Control.Error.Util
import Control.Lens hiding ((??), children, use, op)
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Except
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap as IntMap
import Data.Monoid

-- TODO:
-- * Right now we use simple equality to check types but should implement
--   unification
-- * Be more granular about the capabilities each function needs instead of
--   hardcoding its monad.
-- * What libraries should we be using?
--   - bound
--   - unification-fd
-- * Error messaging is pitiful
--   - show some sort of helpful info
--   - our errors are essentially meaningless
-- * Should type and effect variables share a namespace?

type Var = Int
type TyVar = Int
type EffectVar = Int
type Uid = Int
type Row = Int

-- TODO change to Vector
type Vector a = [a]
type Stack a = [a]

-- Types

data ValTy
  = DataTy Uid (Vector TyArg)
  | SuspendedTy CompTy
  | VariableTy TyVar
  deriving Eq

data CompTy = CompTy
  { compDomain :: Vector ValTy
  , compCodomain :: Peg
  } deriving Eq

data Peg = Peg
  { pegAbility :: Ability
  , pegVal :: ValTy
  } deriving Eq

-- Note: though this is in the CheckM monad, we don't access any state, though
-- we do use the monad to signal failure TODO: is this a lie?. This is called from
-- instantiateTypeVariables, which pulls out the state table for us.
substituteTy :: Vector TyArg -> ValTy -> CheckM ValTy
substituteTy subs =
  let sub = substituteTy subs
      subA = substituteAbility subs
      subArg = todo "subArg"
  in \case
    DataTy uid children -> do
      children' <- forM children subArg
      pure (DataTy uid children')
    SuspendedTy (CompTy domain (Peg ability pVal)) -> do
      ability' <- subA ability
      domain' <- forM domain sub
      pVal' <- sub pVal
      pure (SuspendedTy (CompTy domain' (Peg ability' pVal')))
    VariableTy var -> do
      tyArg <- (subs ^? ix var) ?? FailedVarLookup
      case tyArg of
        TyArgVal val -> pure val
        _ -> throwError FailedVarLookup

substituteArg :: Vector TyArg -> TyArg -> CheckM TyArg
substituteArg subs = \case
  TyArgVal valTy -> TyArgVal <$> substituteTy subs valTy
  TyArgAbility ability -> TyArgAbility <$> substituteAbility subs ability

substituteAbility :: Vector TyArg -> Ability -> CheckM Ability
substituteAbility subs (Ability initiate rows)
  = Ability initiate <$> forM rows mapRow
  where mapRow :: Vector TyArg -> CheckM (Vector TyArg)
        mapRow vals = forM vals (substituteArg subs)

-- We explicitly distinguish between type and effect vars
-- TODO: Use a Value / Effect kind
data TyEffVar = TyVar TyVar | EffVar EffectVar

data TyArg = TyArgVal ValTy | TyArgAbility Ability
  deriving Eq

data Polytype = Polytype
  -- Universally quantify over a bunch of variables
  { polyBinders :: Vector TyEffVar
  -- resulting in a value type
  , polyVal :: ValTy
  }

-- -- A collection of data constructor signatures (which can refer to bound type /
-- -- effect variables).
-- data DataTypeInterface = DataTypeInterface
--   -- we universally quantify over some number of type variables
--   { dataTypeUid :: Uid
--   , dataBinderCount :: Int
--   -- a collection of constructors taking some arguments
--   , constructors :: Vector (Vector ValTy)
--   }
--
-- -- TODO: where should this be used?
-- dataTypeSignature
--   :: DataTypeInterface
--   -> Maybe Ability
--   -> Vector ValTy -- ^ saturate
--   -> Int -- ^ constructor number
--   -> CheckM ValTy
-- dataTypeSignature (DataTypeInterface uid numBinders ctrs) ability args ctrIx = do
--   ctr <- (ctrs ^? ix ctrIx) ?? FailedIndex
--   assert InvalidArgumentCount (length args == numBinders)
--   saturatedArgTys <- mapM (substituteArg args) ctr
--   let dataTy = DataTy uid ability args
--   -- TODO: is this the right ability?
--   pure (SuspendedTy (CompTy saturatedArgTys (Peg emptyAbility dataTy)))

-- commands take arguments (possibly including variables) and return a value
data CommandDeclaration = CommandDeclaration (Vector ValTy) ValTy

data EffectInterface = EffectInterface
  -- we universally quantify some number of type variables
  { binderCount :: Int
  -- a collection of commands
  , commands :: Vector CommandDeclaration
  }

-- -- TODO: where should this be used?
-- effectSignature
--   :: EffectInterface
--   -> Vector ValTy -- ^ saturate
--   -> Int -- ^ command number
--   -> CheckM ValTy
-- effectSignature (EffectInterface numBinders cmds) args cmdIx = do
--   CommandDeclaration cmdArgs cmdRet <- (cmds ^? ix cmdIx) ?? FailedIndex
--   assert InvalidArgumentCount (length args == numBinders)
--   saturatedArgs <- mapM (substituteTy args) cmdArgs
--   saturatedRet <- substituteTy args cmdRet
--   pure (SuspendedTy (CompTy saturatedArgs (Peg emptyAbility saturatedRet)))

data InitiateAbility = OpenAbility EffectVar | ClosedAbility
  deriving Eq

data Ability = Ability InitiateAbility (IntMap (Vector TyArg))
  deriving Eq

-- TODO: This `OpenAbility 0` makes me uncomfortable
emptyAbility :: Ability
emptyAbility = Ability (OpenAbility 0) IntMap.empty

adjustAbility :: Ability -> Adjustment -> Ability
adjustAbility (Ability initiate rows) (Adjustment adjustment) =
  -- union is left-biased and we want to prefer the new interface
  Ability initiate (IntMap.union adjustment rows)

mergeAbility :: Ability -> Ability -> Ability
mergeAbility = todo "mergeAbility"

-- An adjustment is a mapping from effect inferface id to the types it's
-- applied to. IE a set of saturated interfaces.
newtype Adjustment = Adjustment (IntMap {- Uid -> -} (Vector TyArg))
  deriving Monoid

-- Adjustment handlers are a mapping from effect interface id to the handlers
-- for each of that interface's constructors.
data AdjustmentHandlers = AdjustmentHandlers (
  IntMap {- Uid -> -} (Vector Construction')
  )

-- TODO: move all the tables into here
data TypingEnv = TypingEnv (Stack (Either ValTy Polytype))

type DataTypeTable = IntMap (Vector (Vector ValTy))
type VarTyTable = Stack (Either ValTy Polytype) -- IntMap ValTy
type InterfaceTable = IntMap EffectInterface

type CheckM = ExceptT CheckFailure
  (Reader (DataTypeTable, VarTyTable, InterfaceTable, Ability))

-- Terms

data Sort = Use | Construction

type Use' = Tm 'Use
type Construction' = Tm 'Construction

data Tm :: Sort -> * where
  -- inferred
  Variable            :: TyVar                         -> Use'
  InstantiatePolyVar  :: TyVar         -> Vector TyArg -> Use'
  Command             :: Uid           -> Row          -> Use'
  OperatorApplication :: Use'          -> Spine        -> Use'
  Annotation          :: Construction' -> ValTy        -> Use'

  -- checked
  ConstructUse :: Use'                                -> Construction'
  Construct    :: Uid  -> Row -> Vector Construction' -> Construction'
  Lambda       :: Int  -> Construction'               -> Construction'
  Case         :: Use' -> Vector Construction'        -> Construction'
  Handle
    :: Adjustment
    -> Use'
    -> AdjustmentHandlers
    -> Construction'
    -> Construction'
  Let    :: Polytype -> Construction'        -> Construction' -> Construction'
  Letrec :: Polytype -> Vector Construction' -> Construction' -> Construction'

-- type? newtype?
type Spine = Vector Construction'

-- checking

data CheckFailure
  = UnexpectedOperatorTy
  | MismatchingSpineTy
  | TypeMismatch
  | InvalidScrutinee
  | AdjustmentMisalignment
  | UnknownDataConstructor
  | MismatchingConstructorTys
  | MismatchingCaseBranches
  | FailedDataTypeLookup
  | FailedVarLookup
  | FailedPolytypeLookup
  | FailedValTyLookup
  | MismatchingOperatorApplication
  | InvalidAbility
  | InvalidArgumentCount
  | FailedIndex
  | FailedEffectInterfaceLookup
  | InvalidLambdaType
  | FailedSubstitution
  | LambdaTypeMismatch
  | InsufficientScope
  | MismatchingScope
  | PolyvarSaturationMismatch

check :: Construction' -> ValTy -> CheckM ()
check tm ty = case tm of
  ConstructUse use -> do
    inferredTy <- infer use
    when (inferredTy /= ty) (throwError TypeMismatch)
  Construct uid row ctns -> do
    dataCtrs <- lookupDataType uid
    valTys <- (dataCtrs ^? ix row) ?? UnknownDataConstructor
    zipped <- strictZip ctns valTys ?? MismatchingConstructorTys
    forM_ zipped (uncurry check)
  Lambda numBinders body -> case ty of
    SuspendedTy (CompTy dom codom) -> do
      assert LambdaTypeMismatch (length dom == numBinders)
      withValTypes dom (checkWithAmbient body codom)
    _ -> throwError InvalidLambdaType
  Case scrutinee branches -> do
    scrutTy <- infer scrutinee
    case scrutTy of
      DataTy uid _args -> do
        dataRows <- lookupDataType uid
        zipped <- strictZip dataRows branches ?? MismatchingCaseBranches
        forM_ zipped $ \(dataConTys, rhs) ->
          withValTypes dataConTys (check rhs ty)
      _ -> throwError InvalidScrutinee
  Handle adjustment scrutinee handlers fallback -> do
    scrutineeTy <- withAdjustment adjustment $ infer scrutinee
    checkHandlers scrutineeTy ty handlers
    check fallback ty
  Let polyty rhs body -> do
    withTypes [Right polyty] $ check body ty
    check rhs (polyVal polyty)
  Letrec polyty handlers body -> do
    let rhsBodyTy = polyVal polyty -- "A"
    -- let polyvarTy =
    withTypes [Right polyty] $ forM_ handlers (`check` rhsBodyTy)
    check body ty

checkHandlers :: ValTy -> ValTy -> AdjustmentHandlers -> CheckM ()
checkHandlers scrutineeTy expectedTy (AdjustmentHandlers handlers) = do
  iforM_ handlers $ \uid handlerRows ->
    iforM_ handlerRows $ \row handler -> do
      -- TODO: what's the ability supposed to be?
      CompTy dom (Peg ability codom) <- lookupCommandTy uid row
      -- B -> [Sigma]A'
      let contTy = SuspendedTy (CompTy [codom] (Peg ability scrutineeTy))
      withValTypes (dom <> [contTy]) (check handler expectedTy)

-- | Get the types each data constructor holds for this data type.
--
-- Question: should this be parametrized by type parameters / abilities? IE do
-- we allow GADTs?
lookupDataType :: Uid -> CheckM (Vector (Vector ValTy))
lookupDataType uid = asks (^? _1 . ix uid) >>= (?? FailedDataTypeLookup)

lookupEffectInterface :: Uid -> CheckM EffectInterface
lookupEffectInterface uid
  = asks (^? _3 . ix uid) >>= (?? FailedEffectInterfaceLookup)

-- TODO: do we need to instantiate polymorphic variables when looking up?
lookupPolyTy :: TyVar -> CheckM Polytype
lookupPolyTy vId = asks (^? _2 . ix vId . _Right) >>= (?? FailedPolytypeLookup)

lookupValTy :: TyVar -> CheckM ValTy
lookupValTy vId = asks (^? _2 . ix vId . _Left) >>= (?? FailedValTyLookup)

getAmbient :: CheckM Ability
getAmbient = asks (^. _4)

lookupCommandTy :: Uid -> Row -> CheckM CompTy
lookupCommandTy uid row = do
  -- TODO use numBinders? Bind here?
  EffectInterface _numBinders cmds <- lookupEffectInterface uid
  CommandDeclaration domain codomain <- (cmds ^? ix row) ?? FailedIndex
  ability <- getAmbient
  pure (CompTy domain (Peg ability codomain))

checkWithAmbient :: Construction' -> Peg -> CheckM ()
checkWithAmbient tm (Peg ability ty) = withAmbient ability $ check tm ty

withAdjustment :: Adjustment -> CheckM a -> CheckM a
withAdjustment adjustment action = do
  ambient <- getAmbient
  withAmbient (adjustAbility ambient adjustment) action

withAmbient :: Ability -> CheckM a -> CheckM a
withAmbient ability = local (& _4 .~ ability)

-- Push at the front (the top of the stack)
withTypes :: Vector (Either ValTy Polytype) -> CheckM a -> CheckM a
withTypes stack = local (& _2 %~ (stack <>))

withValTypes :: Vector ValTy -> CheckM a -> CheckM a
withValTypes valTys = withTypes (Left <$> valTys)

-- data Polytype = Polytype (Vector TyEffVar) ValTy
-- data TyArg = TyArgVal ValTy | TyArgAbility Ability
-- data TyEffVar = TyVar TyVar | EffVar EffectVar

-- Instantiate type variables (non-recursive). Instantiate effect variables
-- with the ambient ability. This is Theta from the paper.
instantiateTypeVariables :: Polytype -> Vector TyArg -> CheckM ValTy
instantiateTypeVariables (Polytype vars retVal) args = do
  zipped <- strictZip vars args ?? PolyvarSaturationMismatch
  forM_ zipped $ \pairing -> case pairing of
    (TyVar _, TyArgVal _) -> pure ()
    (EffVar _, TyArgAbility _) -> pure ()
    _ -> throwError PolyvarSaturationMismatch

  substituteTy args retVal

infer :: Use' -> CheckM ValTy
infer = \case
  Variable ident -> lookupValTy ident
  -- InstantiatePolyVar  :: TyVar         -> Vector TyArg -> Use'
  InstantiatePolyVar ident args -> do
    polyty <- lookupPolyTy ident
    instantiateTypeVariables polyty args
  Command uid row -> do
    c@(CompTy _domain _codomain) <- lookupCommandTy uid row
    -- TODO make sure sigma is set in the peg
    pure (SuspendedTy c)
  OperatorApplication use spine -> do
    ambient <- getAmbient
    useTy <- infer use
    case useTy of
      SuspendedTy (CompTy domain (Peg ability codomain)) -> do
        when (length domain /= length spine) (throwError MismatchingSpineTy)
        when (ability /= ambient) (throwError InvalidAbility)
        zipped <- strictZip spine domain ?? MismatchingOperatorApplication
        forM_ zipped (uncurry check)
        pure codomain
      _ -> throwError UnexpectedOperatorTy
  Annotation tm valTy -> do
    check tm valTy
    pure valTy


-- evaluation

data Halt
  = UnscopedVariableError
  | UnexpectedToplevelAnnotation
  | UnexpectedApplicand
  | SpineWrongLength

type EvalM = ExceptT Halt (Reader (IntMap Use'))

lookupOp :: Uid -> Row -> EvalM Use'
lookupOp = todo "lookupOp"

step :: Tm a -> EvalM (Tm a)
step (Variable i) = (?? UnscopedVariableError) =<< (asks (^? ix i))
step (InstantiatePolyVar var args) = todo "step InstantiatePolyVar " var args
step (Command interface row) = do
  op <- lookupOp interface row
  step op
-- TODO: check spine is correct length?
step (OperatorApplication use spine) = case use of
  Annotation (Lambda binders body) _type -> todo "fix" $ substitute spine body
  _ -> throwError UnexpectedApplicand

-- TODO justify this rule
step (Annotation _ctr _type) = throwError UnexpectedToplevelAnnotation

step (ConstructUse _) = todo "do this"


substitute :: Spine -> Tm a -> Tm a
substitute = todo "substitute"

-- util

assertM :: Bool -> Maybe ()
assertM valid = if valid then pure () else Nothing

assert :: Monad m => e -> Bool -> ExceptT e m ()
assert reason valid = if valid then pure () else throwError reason

todo :: String -> forall a. a
todo = error

strictZip :: Vector a -> Vector b -> Maybe (Vector (a, b))
strictZip as bs = if length as == length bs then Just (zip as bs) else Nothing

-- TODO: this has to be a standard function
withState' :: MonadState s m => (s -> s) -> m a -> m a
withState' update action = do
  s <- get
  put (update s)
  result <- action
  put s
  pure result
