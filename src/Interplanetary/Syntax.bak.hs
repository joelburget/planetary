

-- checking

type TcM = ExceptT CheckFailure
  (Reader (DataTypeTable, VarTyTable, InterfaceTable, Ability))

runCheckM :: TcM a -> (DataTypeTable, InterfaceTable) -> Either CheckFailure a
runCheckM action (dataTypeTable, interfaceTable) = runReader
  (runExceptT action)
  (dataTypeTable, [], interfaceTable, emptyAbility)

data CheckFailure
  = UnexpectedOperatorTy Use'' ValTy
  | MismatchingSpineTy
  | TypeMismatch
  | InvalidScrutinee
  | AdjustmentMisalignment
  | WrongDataType
  | WrongType Construction'' ValTy
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
  deriving Show

check :: Construction'' -> ValTy -> TcM ()
check tm ty = case tm of
  ConstructUse use -> do
    inferredTy <- infer use
    when (inferredTy /= ty) (throwError TypeMismatch)
  Construct uid row ctns -> do
    case ty of
      DataTy tyUid args -> assert WrongDataType (uid == tyUid)
      _ -> throwError (WrongType tm ty)
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
  Letrec handlers body -> todo "check Letrec"
    -- let rhsBodyTy = polyVal polyty -- "A"
    -- -- let polyvarTy =
    -- withTypes [Right polyty] $ forM_ handlers (`check` rhsBodyTy)
    -- check body ty

checkHandlers :: ValTy -> ValTy -> AdjustmentHandlers -> TcM ()
checkHandlers scrutineeTy expectedTy (AdjustmentHandlers handlers) = do
  iforM_ handlers $ \uid handlerRows ->
    iforM_ handlerRows $ \row handler -> do
      -- TODO: what's the ability supposed to be?
      CompTy dom (Peg ability codom) <- lookupCommandTy uid row
      -- B -> [Sigma]A'
      let contTy = SuspendedTy (CompTy [codom] (Peg ability scrutineeTy))
      withValTypes (dom <> [contTy]) (check handler expectedTy)

lookupEffectInterface :: Uid -> TcM EffectInterface
lookupEffectInterface uid
  = asks (^? _3 . ix uid) >>= (?? FailedEffectInterfaceLookup)

-- TODO: do we need to instantiate polymorphic variables when looking up?
lookupPolyTy :: TyVar -> TcM Polytype
lookupPolyTy vId = asks (^? _2 . ix vId . _Right) >>= (?? FailedPolytypeLookup)

lookupValTy :: TyVar -> TcM ValTy
lookupValTy vId = asks (^? _2 . ix vId . _Left) >>= (?? FailedValTyLookup)

getAmbient :: TcM Ability
getAmbient = asks (^. _4)

lookupCommandTy :: Uid -> Row -> TcM CompTy
lookupCommandTy uid row = do
  -- TODO use numBinders? Bind here?
  EffectInterface _numBinders cmds <- lookupEffectInterface uid
  CommandDeclaration domain codomain <- (cmds ^? ix row) ?? FailedIndex
  ability <- getAmbient
  pure (CompTy domain (Peg ability codomain))

checkWithAmbient :: Construction'' -> Peg -> TcM ()
checkWithAmbient tm (Peg ability ty) = withAmbient ability $ check tm ty

withAdjustment :: Adjustment -> TcM a -> TcM a
withAdjustment adjustment action = do
  ambient <- getAmbient
  withAmbient (adjustAbility ambient adjustment) action

withAmbient :: Ability -> TcM a -> TcM a
withAmbient ability = local (& _4 .~ ability)

-- Push at the front (the top of the stack)
withTypes :: Vector (Either ValTy Polytype) -> TcM a -> TcM a
withTypes stack = local (& _2 %~ (stack <>))

withValTypes :: Vector ValTy -> TcM a -> TcM a
withValTypes valTys = withTypes (Left <$> valTys)

-- data Polytype = Polytype (Vector TyEffVar) ValTy
-- data TyArg = TyArgVal ValTy | TyArgAbility Ability
-- data TyEffVar = TyVar TyVar | EffVar EffectVar

-- Instantiate type variables (non-recursive). Instantiate effect variables
-- with the ambient ability. This is Theta from the paper.
instantiateTypeVariables :: Polytype -> Vector TyArg -> TcM ValTy
instantiateTypeVariables (Polytype binders retVal) args = do
  zipped <- strictZip binders args ?? PolyvarSaturationMismatch
  forM_ zipped $ \pairing -> case pairing of
    (ValTy, TyArgVal _) -> pure ()
    (EffTy, TyArgAbility _) -> pure ()
    _ -> throwError PolyvarSaturationMismatch

  substituteTy args retVal

infer :: Use'' -> TcM ValTy
infer use = case use of
  Variable ident -> lookupValTy ident
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
      _ -> throwError (UnexpectedOperatorTy use useTy)
  Annotation tm valTy -> do
    check tm valTy
    pure valTy


-- evaluation

data Halt
  = UnscopedVariableError
  | UnexpectedToplevelAnnotation
  | UnexpectedApplicand
  | SpineWrongLength

type EvalM = ExceptT Halt (Reader (IntMap Use''))

lookupOp :: Uid -> Row -> EvalM Use''
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

-- Note: though this is in the TcM monad, we don't access any state, though
-- we do use the monad to signal failure TODO: is this a lie?. This is called from
-- instantiateTypeVariables, which pulls out the state table for us.
substituteTy :: Vector TyArg -> ValTy -> TcM ValTy
substituteTy subs =
  let sub = substituteTy subs
      subA = substituteAbility subs
      subArg = substituteArg subs
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

substituteArg :: Vector TyArg -> TyArg -> TcM TyArg
substituteArg subs = \case
  TyArgVal valTy -> TyArgVal <$> substituteTy subs valTy
  TyArgAbility ability -> TyArgAbility <$> substituteAbility subs ability

substituteAbility :: Vector TyArg -> Ability -> TcM Ability
substituteAbility subs (Ability initiate rows)
  = Ability initiate <$> forM rows mapRow
  where mapRow :: Vector TyArg -> TcM (Vector TyArg)
        mapRow vals = forM vals (substituteArg subs)

adjustAbility :: Ability -> Adjustment -> Ability
adjustAbility (Ability initiate rows) (Adjustment adjustment) =
  -- union is left-biased and we want to prefer the new interface
  Ability initiate (IntMap.union adjustment rows)

merkle :: Tm sort -> Use'
merkle = todo "merkle"

-- -- TODO: where should this be used?
-- dataTypeSignature
--   :: DataTypeInterface
--   -> Maybe Ability
--   -> Vector ValTy -- ^ saturate
--   -> Int -- ^ constructor number
--   -> TcM ValTy
-- dataTypeSignature (DataTypeInterface uid numBinders ctrs) ability args ctrIx = do
--   ctr <- (ctrs ^? ix ctrIx) ?? FailedIndex
--   assert InvalidArgumentCount (length args == numBinders)
--   saturatedArgTys <- mapM (substituteArg args) ctr
--   let dataTy = DataTy uid ability args
--   -- TODO: is this the right ability?
--   pure (SuspendedTy (CompTy saturatedArgTys (Peg emptyAbility dataTy)))

-- -- TODO: where should this be used?
-- effectSignature
--   :: EffectInterface
--   -> Vector ValTy -- ^ saturate
--   -> Int -- ^ command number
--   -> TcM ValTy
-- effectSignature (EffectInterface numBinders cmds) args cmdIx = do
--   CommandDeclaration cmdArgs cmdRet <- (cmds ^? ix cmdIx) ?? FailedIndex
--   assert InvalidArgumentCount (length args == numBinders)
--   saturatedArgs <- mapM (substituteTy args) cmdArgs
--   saturatedRet <- substituteTy args cmdRet
--   pure (SuspendedTy (CompTy saturatedArgs (Peg emptyAbility saturatedRet)))
