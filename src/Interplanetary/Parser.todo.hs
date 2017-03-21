

boundEffectVar :: MonadicParsing m => m EffectVar
boundEffectVar = todo "boundEffectVar"

boundVar :: MonadicParsing m => m Var
boundVar = todo "boundVar"

parseUid :: MonadicParsing m => m Uid
parseUid = todo "parseUid"

-- entry points:
-- * parseDataT
-- * parseInterface
-- * parseDecl

parseDecl :: MonadicParsing m => m (Construction', ValTy)
parseDecl = do
  name <- boundVar
  colon
  ty <- parseSigType
  construction <- localIndentation Gt $ do
    assign
    parseRawTm
  pure (construction, ty)

parseDataT :: MonadicParsing m => m DataTypeInterface
parseDataT = do
  reserved "data"
  tyArgs <- many parseTyArg
  assign
  (kinds, ctrs) <- inBoundTys tyArgs (localIndentation Gt parseConstructors)
  return $ DataTypeInterface (todo "Uid") kinds ctrs

inBoundTys :: MonadicParsing m => Vector TyArg -> m a -> m (Vector Kind, a)
inBoundTys = todo "inBoundTys"

parseConstructors :: MonadicParsing m => m [DataConstructor]
parseConstructors = sepBy parseCtr bar

parseCtr :: MonadicParsing m => m DataConstructor
parseCtr = DataConstructor <$> many parseValTy'

-- As the outer braces are optional in top-level signatures we require
-- that plain pegs must have explicit ability brackets.
--
-- The following collections of signatures are equivalent:
--
--   f : {A -> B -> C}  and  f : A -> B -> C
--   x : {Int}  and  x : {[]Int}  and x : []Int
--
-- A signature of the form
--
--   x : Int
--
-- is not currently valid. Once we add support for top level values it
-- will become valid, but will not mean the same thing as:
--
--   x : []Int
parseSigType :: MonadicParsing m => m ValTy
parseSigType = todo "parseSigType"

parseCompTy :: MonadicParsing m => m CompTy
parseCompTy = CompTy
  <$> many (try (parseValTy <* arr))
  <*> parsePeg

parseInterface :: MonadicParsing m => m EffectInterface
parseInterface = do
  reserved "interface"
  tyVars <- many parseTyVar
  assign
  -- inBoundTys
  xs <- localIndentation Gt $ sepBy1 parseCmd bar
  return (EffectInterface tyVars xs)

parseCmd :: MonadicParsing m => m CommandDeclaration
parseCmd = do
  (xs, y) <- parseCmdType
  return (CommandDeclaration xs y)

-- only value arguments and result type
parseCmdType :: MonadicParsing m => m (Vector ValTy, ValTy)
parseCmdType = do
  vs <- sepBy1 parseValTy arr
  -- TODO: use unsnoc
  return (init vs, last vs)

parsePeg :: MonadicParsing m => m Peg
parsePeg = Peg <$> parseAbility <*> parseValTy

parsePegExplicit :: MonadicParsing m => m Peg
parsePegExplicit = Peg <$> brackets parseAbilityBody <*> parseValTy

parseAdj :: MonadicParsing m => m Adjustment
parseAdj = do
  mxs <- optional $ angles (sepBy parseAdj' comma)
  return $ Adjustment $ IntMap.fromList $ maybe [] id mxs

parseAdj' :: MonadicParsing m => m (TyVar, Vector TyArg)
parseAdj' = (,) <$> boundTyVar <*> many parseTyArg

parseInterfaceInstances :: MonadicParsing m => m [(Uid, [TyArg])]
parseInterfaceInstances = sepBy parseInterfaceInstance comma

-- 0 | 0|Interfaces | E|Interfaces | Interfaces
parseAbilityBody :: MonadicParsing m => m Ability
parseAbilityBody =
  let closed = do
        symbol "0"
        xs <- option [] (bar *> parseInterfaceInstances)
        return $ Ability ClosedAbility (IntMap.fromList xs)
      var = do
        e <- option emptyAbility (try $ boundEffectVar <* bar)
        xs <- parseInterfaceInstances
        return $ Ability e (IntMap.fromList xs)
  in closed <|> var

parseAbility :: MonadicParsing m => m Ability
parseAbility = do
  mxs <- optional $ brackets parseAbilityBody
  return $ maybe (Ability emptyAbility IntMap.empty) id mxs

parseInterfaceInstance :: MonadicParsing m => m (Uid, [TyArg])
parseInterfaceInstance = (,) <$> parseUid <*> many parseTyArg

-- Parse a potential datatype. Note it may actually be a type variable.
parseDataTy :: MonadicParsing m => m ValTy
parseDataTy = DataTy
  <$> parseUid
  <*> localIndentation Gt (many parseTyArg)

parseValTy :: MonadicParsing m => m ValTy
parseValTy = try parseDataTy <|> parseValTy'

parseRawTm :: MonadicParsing m => m Construction'
parseRawTm = parseLet <|> parseLetRec <|> parseRawTm'

parseLet :: MonadicParsing m => m Construction'
parseLet = do
  reserved "let"
  ty <- parsePolyty
  assign
  rhs <- parseRawTm
  reserved "in"
  body <- parseRawTm
  return $ Let ty rhs body

parseLetRec :: MonadicParsing m => m Construction'
parseLetRec = do
  reserved "letrec"
  definitions <- sequence $ do
    x <- identifier
    colon
    ty <- parsePolyty
    assign
    (ty,) <$> parseRawTm
  reserved "in"
  body <- parseRawTm
  return $ Letrec definitions body

parsePolyty :: MonadicParsing m => m Polytype
parsePolyty = todo "parsePolyty"

parseRawTm' :: MonadicParsing m => m Construction'
parseRawTm' = choice
  [ try parseApplication
  , Variable <$> boundVar
  ]

parseApplication :: MonadicParsing m => m Construction'
parseApplication = OperatorApplication
  <$> identifier
  <*> choice [some parseRawTm', bang >> pure []]

evalCharIndentationParserT
  :: Monad m => CoreParser Char m a -> IndentationState -> m a
evalCharIndentationParserT = evalIndentationParserT . runCoreParser

evalTokenIndentationParserT
  :: Monad m => CoreParser Token m a -> IndentationState -> m a
evalTokenIndentationParserT = evalIndentationParserT . runCoreParser

runParse ev p input
 = let indA = ev p $ mkIndentationState 0 infIndentation True Ge
   in case parseString indA mempty input of
    Failure err -> Left (show err)
    Success t -> Right t

--runCharParse = runParse evalCharIndentationParserT
runTokenParse p = runParse evalTokenIndentationParserT p
