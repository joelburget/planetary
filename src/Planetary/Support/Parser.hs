{-# language ConstraintKinds #-}
{-# language DataKinds #-}
{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language NamedFieldPuns #-}
{-# language PackageImports #-}
{-# language StandaloneDeriving #-}
{-# language TupleSections #-}
{-# language TypeApplications #-}
-- A simple Core Frank parser based on the frankjnr implementation
module Planetary.Support.Parser where

import Control.Applicative
import Control.Lens (unsnoc)
import Data.ByteString (ByteString)
import Data.Functor (($>))
import Data.Int (Int64)
import Data.Maybe (fromMaybe)

-- TODO: be suspicious of `try`, see where it can be removed
-- http://blog.ezyang.com/2014/05/parsec-try-a-or-b-considered-harmful/
import Text.Trifecta hiding (parens) -- hiding (try)
import Text.Trifecta.Delta hiding (delta)
import "indentation-trifecta" Text.Trifecta.Indentation

import Data.Char

import qualified Text.Parser.Token as Tok
import Text.Parser.Token.Style
import qualified Text.Parser.Token.Highlight as Hi
import qualified Data.HashSet as HashSet

import Planetary.Core
import Planetary.Util

newtype CoreParser t m a =
  CoreParser { runCoreParser :: IndentationParserT t m a }
  deriving (Functor, Alternative, Applicative, Monad, Parsing
           , IndentationParsing)

deriving instance DeltaParsing m => CharParsing (CoreParser Char m)
deriving instance DeltaParsing m => CharParsing (CoreParser Token m)
deriving instance DeltaParsing m => TokenParsing (CoreParser Char m)

instance DeltaParsing m => TokenParsing (CoreParser Token m) where
  someSpace = CoreParser $ buildSomeSpaceParser someSpace haskellCommentStyle
  nesting = CoreParser . nesting . runCoreParser
  semi = CoreParser $ runCoreParser semi
  highlight h = CoreParser . highlight h . runCoreParser
  token p = (CoreParser $ token (runCoreParser p)) <* whiteSpace

type MonadicParsing m = (TokenParsing m, IndentationParsing m, Monad m)

planetaryStyle :: MonadicParsing m => IdentifierStyle m
planetaryStyle = IdentifierStyle {
    _styleName = "Planetary"
  , _styleStart = satisfy (\c -> isAlphaNum c || c == '_' || c == '$')
  , _styleLetter = satisfy (\c -> isAlphaNum c || c == '_' || c == '\'')
  , _styleReserved = HashSet.fromList
    [ "data"
    , "interface"
    , "let"
    , "letrec"
    , "in"
    , "forall"
    , "case"
    , "handle"
    , "of"
    , "with"
    ]
  , _styleHighlight = Hi.Identifier
  , _styleReservedHighlight = Hi.ReservedIdentifier }

arr, bar, assign, bang :: MonadicParsing m => m String
arr    = symbol "->"
bar    = symbol "|"
assign = symbol "="
bang   = symbol "!"

parens :: MonadicParsing m => m a -> m a
parens = Tok.parens . localIndentation Any

reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve planetaryStyle

identifier :: MonadicParsing m => m String
identifier = Tok.ident planetaryStyle
  <?> "identifier"

-- TODO: get an exact count of digits
parseUid :: MonadicParsing m => m String
parseUid = identifier
  -- (('$':) <$> (string "$" *> identifier) <|>
  --  (string "d" *> symbol "%" *> some alphaNum))
  <?> "uid"

parseValTy :: MonadicParsing m => m (ValTy String String)
parseValTy = parseDataTy <|> parseValTyNoAp
  <?> "Val Ty"

parseValTyNoAp :: MonadicParsing m => m (ValTy String String)
parseValTyNoAp = parens parseValTy
          <|> SuspendedTy <$> braces parseCompTy
          <|> VariableTy  <$> identifier
          <?> "Val Ty (not data)"

parseTyArg :: MonadicParsing m => m (TyArg String String)
parseTyArg = TyArgVal     <$> parseValTyNoAp
         <|> TyArgAbility <$> brackets parseAbilityBody
         <?> "Ty Arg"

parseConstructors :: MonadicParsing m => m (Vector (ConstructorDecl String String))
parseConstructors = sepBy parseConstructor bar <?> "Constructors"

parseConstructor :: MonadicParsing m => m (ConstructorDecl String String)
parseConstructor = ConstructorDecl <$> many parseValTyNoAp <?> "Constructor"

-- Parse a potential datatype. Note it may actually be a type variable.
parseDataTy :: MonadicParsing m => m (ValTy String String)
parseDataTy = angles $ DataTy
  <$> parseUid
  <*> many parseTyArg
  -- <*> localIndentation Gt (many parseTyArg)
  <?> "Data Ty"

parseTyVar :: MonadicParsing m => m (String, Kind)
parseTyVar = (,EffTy) <$> brackets identifier
         <|> (,ValTy) <$> identifier
         <?> "Ty Var"

-- 0 | 0|Interfaces | e|Interfaces | Interfaces
-- TODO: change to comma?
-- TODO: allow explicit e? `[e]`
parseAbilityBody :: MonadicParsing m => m (Ability String String)
parseAbilityBody =
  let closedAb = do
        _ <- symbol "0"
        instances <- option [] (bar *> parseInterfaceInstances)
        return $ Ability ClosedAbility (uIdMapFromList @String instances)
      varAb = do
        var <- option "e" (try identifier)
        instances <- option [] (bar *> parseInterfaceInstances)
        return $ Ability OpenAbility (uIdMapFromList @String instances)
  in closedAb <|> varAb <?> "Ability Body"

parseAbility :: MonadicParsing m => m (Ability String String)
parseAbility = do
  mxs <- optional $ brackets parseAbilityBody
  return $ fromMaybe emptyAbility mxs

-- liftClosed :: (Traversable f, Alternative m) => f String -> m (f Int)
-- liftClosed tm = case closed tm of
--   Nothing -> empty
--   Just tm' -> pure tm'

parsePeg :: MonadicParsing m => m (Peg String String)
parsePeg = Peg
  <$> parseAbility
  <*> parseValTy
  <?> "Peg"

parseCompTy :: MonadicParsing m => m (CompTy String String)
parseCompTy = CompTy
  <$> many (try (parseValTy <* arr)) -- TODO: bad use of try
  <*> parsePeg
  <?> "Comp Ty"

parseInterfaceInstance :: MonadicParsing m => m (String, [TyArg String String])
parseInterfaceInstance = angles $ (,)
  <$> parseUid
  <*> many parseTyArg
  <?> "Interface Instance"

parseInterfaceInstances :: MonadicParsing m => m [(String, [TyArg String String])]
parseInterfaceInstances = sepBy parseInterfaceInstance comma
  <?> "Interface Instances"

parseDataDecl :: MonadicParsing m => m DataDeclS
parseDataDecl = do
  reserved "data"
  name <- identifier
  tyArgs <- many parseTyVar
  _ <- assign
  ctrs <- localIndentation Gt (absoluteIndentation parseConstructors)
  return (DataDecl name (DataTypeInterface tyArgs ctrs))

-- only value arguments and result type
parseCommandType
  :: MonadicParsing m
  => m (Vector (ValTy String String), ValTy String String)
parseCommandType = do
  vs <- sepBy1 parseValTy arr
  maybe empty pure (unsnoc vs)
  -- maybe empty pure . unsnoc =<< sepBy1 parseValTy arr

parseCommandDecl :: MonadicParsing m => m (CommandDeclaration String String)
parseCommandDecl = uncurry CommandDeclaration <$> parseCommandType
  <?> "Command Decl"

parseInterfaceDecl :: MonadicParsing m => m InterfaceDeclS
parseInterfaceDecl = (do
  reserved "interface"
  name <- identifier
  tyVars <- many parseTyVar
  _ <- assign
  -- inBoundTys
  xs <- localIndentation Gt $ absoluteIndentation $ sepBy1 parseCommandDecl bar
  return (InterfaceDecl name (EffectInterface tyVars xs))
  ) <?> "Interface Decl"

parseDecls :: MonadicParsing m => m [DeclS]
parseDecls = some (choice
  [ DataDecl_      <$> parseDataDecl
  , InterfaceDecl_ <$> parseInterfaceDecl
  , TermDecl_      <$> parseTermDecl
  ]) <?> "Data or Interface Decls"

-- TODO allow a more succinct form of `x = letrec x = ... in x`
-- ... `letrec x =
-- ... this could be generalizd to let (but that would cost the complexity of
-- multiple types of toplevel)
parseTermDecl :: MonadicParsing m => m TermDeclS
parseTermDecl =
  let parser = TermDecl <$> identifier <* assign <*> parseLetrec
  in parser <?> "definition"

reorgTuple :: (a, b, c) -> (a, (b, c))
reorgTuple (a, b, c) = (a, (b, c))

parseLetrec :: MonadicParsing m => m Tm'
parseLetrec =
  let parser = do
        reserved "letrec"
        definitions <- localIndentation Gt $ absoluteIndentation $ some $ (,,)
          <$> identifier <* colon
          <*> parsePolyty <* assign
          <*> parseLambda <* dot
        reserved "in"
        body <- parseTm
        let (names, binderVals) = unzip (reorgTuple <$> definitions)
        return $ letrec names binderVals body
  in parser <?> "Letrec"

parsePolyty :: MonadicParsing m => m Polytype'
parsePolyty = do
  reserved "forall"
  args <- many parseTyVar
  _ <- dot
  result <- parseValTy
  pure (PolytypeP args result)

parseLet :: MonadicParsing m => m Construction
parseLet =
  let parser = do
        reserved "let"
        name <- identifier
        _ <- colon
        ty <- parsePolyty
        _ <- assign
        rhs <- parseTm
        reserved "in"
        body <- parseTm
        pure (let_ name ty rhs body)
  in parser <?> "Let"

parseValue :: MonadicParsing m => m Value'
parseValue = choice
  -- [ parseDataConstructor
  -- parseCommand
  [ parseLambda
  ]

parseCase :: MonadicParsing m => m Tm'
parseCase = do
  _ <- reserved "case"
  m <- parseTm
  _ <- reserved "of"
  (uid, branches) <- localIndentation Gt $ do
    uid <- parseUid
    _ <- colon

    branches <- localIndentation Gt $ absoluteIndentation $ many $ do
      _ <- bar
      vars <- many identifier
      _ <- arr
      rhs <- parseTm
      pure (vars, rhs)
    pure (uid, branches)
  pure $ Cut (CaseP uid branches) m

parseHandle :: MonadicParsing m => m Tm'
parseHandle = do
  _ <- reserved "handle"
  adj <- parens parseAdjustment
  -- TODO: "returning"?
  peg <- parens parsePeg
  target <- parseTm
  _ <- reserved "with"

  (effectHandlers, valueHandler) <- localIndentation Gt $ absoluteIndentation $ do
    effectHandlers <- many $ do
      uid <- parseUid
      _ <- colon

      rows <- localIndentation Gt $ absoluteIndentation $ many $ do
        _ <- bar
        vars <- many identifier
        _ <- arr
        kVar <- identifier
        _ <- arr
        rhs <- parseTm
        pure (vars, kVar, rhs)

      pure (uid, rows)

    valueHandler <- do
      _ <- bar
      var <- identifier
      _ <- arr
      rhs <- parseTm
      pure (var, rhs)

    pure (uIdMapFromList @String effectHandlers, valueHandler)

  let cont = handle adj peg effectHandlers valueHandler
  pure Cut {cont, target}

parseTm :: MonadicParsing m => m Tm'
parseTm = (do
  tms <- some parseTmNoApp
  -- "We write '!' for the empty spine"
  hasBang <- (bang $> True) <|> pure False
  case (tms, hasBang) of
    ([],           _) -> empty
    ([tm],      True) -> pure (Cut (Application []) tm)
    (_,         True) -> empty
    ([tm],     False) -> pure tm
    (tm:spine, False) -> pure (Cut (Application spine) tm)
  ) <?> "Tm"

parseApplication :: MonadicParsing m => m Use
parseApplication =
  let parser = do
        fun <- Variable <$> identifier -- TODO: not sure this line is right
        spine <- choice [some parseTmNoApp, bang $> []]
        pure $ Cut (Application spine) fun
  in parser <?> "Application"

parseTmNoApp :: MonadicParsing m => m Tm'
parseTmNoApp = choice
  [ parens parseTm
  , Value <$> parseValue
  , parseCase
  , parseHandle
  , parseLet
  , parseLetrec
  , Variable <$> identifier
  ] <?> "Tm (no app)"

parseAdjustment :: MonadicParsing m => m (Adjustment String String)
parseAdjustment = (do
  -- Same as parseInterfaceInstance
  let adjItem = angles $ (,) <$> parseUid <*> many parseTyArg
  rows <- adjItem `sepBy1` symbol "+"
  pure $ Adjustment $ uIdMapFromList @String rows
  ) <?> "Adjustment"

-- parseContinuation

parseLambda :: MonadicParsing m => m Value'
parseLambda = Lam
  <$> (symbol "\\" *> some identifier) <*> (arr *> parseTm)
  <?> "Lambda"

evalCharIndentationParserT
  :: Monad m => CoreParser Char m a -> IndentationState -> m a
evalCharIndentationParserT = evalIndentationParserT . runCoreParser

evalTokenIndentationParserT
  :: Monad m => CoreParser Token m a -> IndentationState -> m a
evalTokenIndentationParserT = evalIndentationParserT . runCoreParser

data ParseLocation = ParseLocation !ByteString !Int64 !Int64

testLocation :: ParseLocation
testLocation = ParseLocation "(test)" 0 0

lowLevelRunParse
  :: (t -> IndentationState -> Parser b)
  -> t
  -> ParseLocation
  -> String
  -> Either String b
lowLevelRunParse ev p (ParseLocation filename row col) input
 = let indA = ev p $ mkIndentationState 0 infIndentation True Ge
       delta = Directed filename row col 0 0
   in case parseString indA delta input of
        Failure (ErrInfo errDoc _deltas) -> Left (show errDoc)
        Success t -> Right t

runTokenParse
  :: CoreParser Token Parser b -> ParseLocation -> String -> Either String b
runTokenParse = lowLevelRunParse evalTokenIndentationParserT
