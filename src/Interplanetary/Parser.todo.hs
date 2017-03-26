

-- entry points:
-- * parseDataDecl
-- * parseInterface
-- * parseDecl

parseAdj :: MonadicParsing m => m Adjustment
parseAdj = do
  mxs <- optional $ angles (sepBy parseAdj' comma)
  return $ Adjustment $ IntMap.fromList $ maybe [] id mxs

parseAdj' :: MonadicParsing m => m (TyVar, Vector TyArg)
parseAdj' = (,) <$> boundTyVar <*> many parseTyArg
