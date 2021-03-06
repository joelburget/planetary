{-# language ConstraintKinds #-}
{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language FlexibleInstances #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language MultiParamTypeClasses #-}
{-# language NamedFieldPuns #-}
{-# language OverloadedStrings #-}
{-# language PackageImports #-}
{-# language StandaloneDeriving #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
{-# language TupleSections #-}
-- A simple Core Frank parser
module Planetary.Support.Parser where

import Control.Applicative
import Control.Lens (unsnoc)
import Control.Monad.Trans (MonadTrans(lift))
import Control.Monad.State.Strict
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B8
import Data.Int (Int64)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Text.Encoding (encodeUtf8)
import qualified Network.IPLD as IPLD
import Network.IPLD (Cid, IsIpld(..), valueCid, compact)

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

type Ability'            = Ability Text
type CompTy'             = CompTy Text
type ConstructorDecl'    = ConstructorDecl Text
type Peg'                = Peg Text
type Polytype'           = Polytype Text
type TyArg'              = TyArg Text
type ValTy'              = ValTy Text
type Tm'                 = Tm Text

newtype CoreParser t m a =
  CoreParser { runCoreParser :: IndentationParserT t (StateT ValueStore m) a }
  deriving (Functor, Alternative, Applicative, Monad, Parsing
           , IndentationParsing, MonadPlus)

deriving instance DeltaParsing m => CharParsing (CoreParser Char m)
deriving instance DeltaParsing m => CharParsing (CoreParser Token m)
deriving instance DeltaParsing m => TokenParsing (CoreParser Char m)

instance Monad m => MonadState ValueStore (CoreParser t m) where
  get   = CoreParser $ lift get
  put s = CoreParser $ lift (put s)

instance DeltaParsing m => TokenParsing (CoreParser Token m) where
  someSpace   = CoreParser $ buildSomeSpaceParser someSpace haskellCommentStyle
  nesting     = CoreParser . nesting . runCoreParser
  semi        = CoreParser $ runCoreParser semi
  highlight h = CoreParser . highlight h . runCoreParser
  token p     = (CoreParser $ token (runCoreParser p)) <* whiteSpace

type MonadicParsing m
  = (TokenParsing m, IndentationParsing m, Monad m, MonadState ValueStore m)

planetaryStyle :: MonadicParsing m => IdentifierStyle m
planetaryStyle = IdentifierStyle {
    _styleName = "Planetary"
  , _styleStart  = satisfy (\c -> isAlphaNum c || c == '_' || c == '$')
  , _styleLetter = satisfy (\c -> isAlphaNum c || c == '_' || c == '\'')
  , _styleReserved = HashSet.fromList
    -- TODO: data and interface aren't really reserved from the term language
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

arr, bar, assign, bang :: MonadicParsing m => m Text
arr    = textSymbol "->"
bar    = textSymbol "|"
assign = textSymbol "="
bang   = textSymbol "!"

indentedBlock :: MonadicParsing m => m a -> m a
indentedBlock = localIndentation Gt

parens :: MonadicParsing m => m a -> m a
parens = Tok.parens . localIndentation Any

reserved :: MonadicParsing m => Text -> m ()
reserved = Tok.reserveText planetaryStyle

identifier :: MonadicParsing m => m Text
identifier = Tok.ident planetaryStyle
  <?> "identifier"

-- TODO: get an exact count of digits
parseUid :: MonadicParsing m => m Text
parseUid = identifier <?> "uid"

parseValTy :: MonadicParsing m => m (TyFix Text)
parseValTy = choice
  [ parseDataTy
  , parens parseValTy
  , SuspendedTy <$> braces parseCompTy
  , VariableTy  <$> identifier
  ] <?> "Val Ty"

parseTyArg :: MonadicParsing m => m TyArg'
parseTyArg = TyArgAbility <$> brackets parseAbilityBody
         <|> TyArgVal     <$> parseValTy
         <?> "Ty Arg"

parseConstructor
  :: MonadicParsing m => Vector TyArg' -> m ConstructorDecl'
parseConstructor tyArgs = angles (ConstructorDecl
  <$> identifier
  <*> many parseValTy
  <*> pure tyArgs
  ) <?> "Constructor"

parseDataTy :: MonadicParsing m => m ValTy'
parseDataTy = angles $ DataTy
  <$> (VariableTy <$> parseUid)
  <*> many parseTyArg
  -- <*> localIndentation Gt (many parseTyArg)
  <?> "Data Ty"

parseTyVar :: MonadicParsing m => m (Text, Kind)
parseTyVar = (,EffTyK) <$> brackets identifier
         <|> (,ValTyK) <$> identifier
         <?> "Ty Var"

-- 0 | 0,Interfaces | e,Interfaces | Interfaces
-- TODO: allow explicit e? `[e]`
parseAbilityBody :: MonadicParsing m => m Ability'
parseAbilityBody =
  let closedAb = do
        _ <- textSymbol "0"
        skipOptional comma
        instances <- option [] parseInterfaceInstances
        return $ Ability ClosedAbility (fromList instances)
      varAb = do
        var <- option ("e" :: Text) (try identifier)
        skipOptional comma
        instances <- parseInterfaceInstances
        return $ Ability OpenAbility (fromList instances)
  in closedAb <|> varAb <?> "Ability Body"

parseAbility :: MonadicParsing m => m Ability'
parseAbility = do
  mxs <- optional $ brackets parseAbilityBody
  return $ fromMaybe emptyAbility mxs

parsePeg :: MonadicParsing m => m Peg'
parsePeg = Peg
  <$> parseAbility
  <*> parseValTy
  <?> "Peg"

parseCompTy :: MonadicParsing m => m (CompTy Text)
parseCompTy = CompTy
  <$> many (try (parseValTy <* arr)) -- TODO: bad use of try
  <*> parsePeg
  <?> "Comp Ty"

parseInterfaceInstance :: MonadicParsing m => m (Text, [TyArg'])
parseInterfaceInstance = angles $ (,)
  <$> parseUid
  <*> many parseTyArg
  <?> "Interface Instance"

parseInterfaceInstances :: MonadicParsing m => m [(Text, [TyArg'])]
parseInterfaceInstances = parseInterfaceInstance `sepBy` comma
  <?> "Interface Instances"

parseDataDecl :: MonadicParsing m => m (DataDecl Text)
parseDataDecl = do
  reserved "data"
  name <- identifier
  tyArgs <- many parseTyVar
  _ <- assign

  -- this is the result type each constructor will saturate to
  let tyArgs' = map (\(name', _) -> (TyArgVal (VariableTy name'))) tyArgs

  -- put bindingState
  ctrs <- indentedBlock
    (many (absoluteIndentation (bar *> parseConstructor tyArgs')))
  return (DataDecl name (DataTypeInterface tyArgs ctrs))

-- only value arguments and result type
parseCommandType
  :: MonadicParsing m
  => m (Text, Vector ValTy', ValTy')
parseCommandType = do
  name <- identifier
  _ <- colon
  vs <- sepBy1 parseValTy arr
  (args, result) <- maybe empty pure (unsnoc vs)
  pure (name, args, result)

parseCommandDecl :: MonadicParsing m => m (CommandDeclaration Text)
parseCommandDecl = bar >> (uncurry3 CommandDeclaration <$> parseCommandType)
  <?> "Command Decl"

parseInterfaceDecl :: MonadicParsing m => m (InterfaceDecl Text)
parseInterfaceDecl = (do
  reserved "interface"
  name <- identifier
  tyVars <- many parseTyVar
  _ <- assign
  -- inBoundTys
  xs <- indentedBlock (many (absoluteIndentation parseCommandDecl))
  return (InterfaceDecl name (EffectInterface tyVars xs))
  ) <?> "Interface Decl"

parseDecls :: MonadicParsing m => m [Decl Text]
parseDecls = some (choice
  [ DataDecl_      <$> parseDataDecl
  , InterfaceDecl_ <$> parseInterfaceDecl
  , TermDecl_      <$> parseTermDecl
  ]) <?> "Data or Interface Decls"

-- TODO allow a more succinct form of `x = letrec x = ... in x`
-- ... `letrec x =
-- ... this could be generalizd to let (but that would cost the complexity of
-- multiple types of toplevel)
parseTermDecl :: MonadicParsing m => m (TermDecl Text)
parseTermDecl =
  let parser = TermDecl <$> identifier <* assign <*> parseLetrec
  in parser <?> "definition"

parseLetrec :: MonadicParsing m => m Tm'
parseLetrec =
  let parser = do
        reserved "letrec"
        definitions <- indentedBlock $ many $ absoluteIndentation $ do
          name <- identifier
          tyAndDef <- indentedBlock $ absoluteIndentation $ (,)
            <$> (colon *> parsePolyty)
            <*> (assign *> parseLambda)
          pure (name, tyAndDef)

        reserved "in"
        body <- indentedBlock parseTm
        let (names, binderVals) = unzip definitions
        return $ Letrec names binderVals body
  in parser <?> "Letrec"

parsePolyty :: MonadicParsing m => m Polytype'
parsePolyty = do
  reserved "forall"
  args <- many parseTyVar
  _ <- dot
  result <- parseValTy
  pure (Polytype args result)

parseLet :: MonadicParsing m => m Tm'
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
        pure (Let rhs ty name body)
  in parser <?> "Let"

parseValue :: MonadicParsing m => m Tm'
parseValue = choice
  [ parseDataConstructor
  , parseText
  -- parseCommand
  , parseLambda
  ] <?> "Value"

mkForeign :: IsIpld a => a -> (Cid, IPLD.Value)
mkForeign val = let val' = toIpld val in (valueCid val', val')

mkForeignTm :: IsIpld a => Cid -> Vector ValTyI -> a -> (TmI, IPLD.Value)
mkForeignTm tyId tySat a =
  let (cid, val) = mkForeign a
  in (ForeignValue tyId tySat cid, val)

parseText :: MonadicParsing m => m Tm'
parseText = do
  str <- stringLiteral
  let (cid, ipldVal) = mkForeign @Text str
  modify (storeOf [ipldVal] <>)
  pure (ForeignValue "Text" [] (cidText cid))

cidText :: Cid -> Text
cidText = T.pack . B8.unpack . compact

parseDataConstructor :: MonadicParsing m => m Tm'
parseDataConstructor = angles (DataConstructor
  <$> parseUid <* dot
  <*> (fromIntegral <$> natural)
  <*> many parseTmNoApp
  ) <?> "Data constructor"

parseCase :: MonadicParsing m => m Tm'
parseCase =
  let parser = do
        _ <- reserved "case"
        m <- parseTm
        _ <- reserved "of"
        branches <- localIndentation Any $ absoluteIndentation $ many $ do
          _ <- bar
          idents <- angles $ some identifier
          _ <- arr
          rhs <- parseTm
          let _uncheckedName:vars = idents
          pure (vars, rhs)
        pure $ Case m branches
  in parser <?> "case"

parseHandle :: MonadicParsing m => m Tm'
parseHandle = (do
  _ <- reserved "handle"
  scrutinee <- parseTm
  _ <- colon
  peg <- parsePeg
  _ <- reserved "with"

  (effectHandlers, adjustment, valueHandler) <- indentedBlock $ do
    effectHandlers <- many $ absoluteIndentation $ do
      uid <- parseUid
      tyArgs <- many parseTyArg
      _ <- colon

      rows <- indentedBlock $ many $ do
        _ <- bar
        (idents, kVar) <- angles $ (,)
          <$> some identifier <* arr
          <*> identifier
        _ <- arr
        rhs <- parseTm
        let _uncheckedName:vars = idents
        pure (vars, kVar, rhs)

      pure (uid, tyArgs, rows)

    valueHandler <- absoluteIndentation $ do
      _ <- bar
      var <- identifier
      _ <- arr
      rhs <- parseTm
      pure (var, rhs)

    let handlers = fromList $
          (\(uid, _, rows) -> (uid, rows)) <$> effectHandlers
        adjustment = Adjustment $ fromList $
          (\(uid, tyArgs, _) -> (uid, tyArgs)) <$> effectHandlers

    pure (handlers, adjustment, valueHandler)

  pure $ Handle scrutinee adjustment peg effectHandlers valueHandler
  ) <?> "handle"

parseTm :: MonadicParsing m => m Tm'
parseTm = (do
  tms <- some $ do
    tm <- parseTmNoApp

    -- "We write '!' for the empty spine"
    (AppT tm [] <$ bang) <|> pure tm

  case tms of
    [] -> empty
    [tm] -> pure tm
    fun:spine -> pure $ AppT fun spine
  ) <?> "Tm"

parseTmOrAnnot :: MonadicParsing m => m Tm'
parseTmOrAnnot =
  let p1 = do
        val <- parseValue
        maybeTy <- optional $ try $ do
          _ <- colon
          parseValTy
        pure $ case maybeTy of
          Nothing -> val
          Just ty -> Annotation val ty
      p2 = parseTm
  in p1 <|> p2 <?> "term or annot"

parseTmNoApp :: MonadicParsing m => m Tm'
parseTmNoApp = choice
  [ parens parseTmOrAnnot
  , parseValue
  , parseCase
  , parseHandle
  , parseLet
  , parseLetrec
  , parseCommandOrIdent
  ] <?> "Tm (no app)"

parseCommandOrIdent :: MonadicParsing m => m Tm'
parseCommandOrIdent = do
  name <- identifier

  dotRow <- optional $ try $ do
    _ <- dot
    natural

  hasBang <- optional $ try bang

  let v = case dotRow of
        Just row -> Command name (fromIntegral row)
        Nothing -> Variable name
  let v' = case hasBang of
        Just _bang -> AppT v []
        Nothing -> v
  pure v'

  -- TODO: named commands
  -- TODO application of terms

parseLambda :: MonadicParsing m => m Tm'
parseLambda = Lambda
  <$> (textSymbol "\\" *> many identifier) <*> (arr *> parseTm)
  <?> "Lambda"

evalCharIndentationParserT
  :: Monad m => CoreParser Char m a -> IndentationState -> m (a, ValueStore)
evalCharIndentationParserT p i = runStateT (evalIndentationParserT (runCoreParser p) i) mempty

evalTokenIndentationParserT
  :: Monad m => CoreParser Token m a -> IndentationState -> m (a, ValueStore)
evalTokenIndentationParserT p i = runStateT (evalIndentationParserT (runCoreParser p) i) mempty

data ParseLocation = ParseLocation !ByteString !Int64 !Int64

testLocation, forceLocation :: ParseLocation
testLocation = ParseLocation "(test)" 0 0
forceLocation = ParseLocation "(force)" 0 0

lowLevelRunParse
  :: (t -> IndentationState -> Parser b)
  -> t
  -> ParseLocation
  -> Text
  -> Either String b
lowLevelRunParse ev p (ParseLocation filename row col) input
 = let indA = ev p $ mkIndentationState 0 infIndentation True Ge
       delta = Directed filename row col 0 0
   in case parseByteString indA delta (encodeUtf8 input) of
        Failure (ErrInfo errDoc _deltas) -> Left (show errDoc)
        Success t -> Right t

runTokenParse
  :: CoreParser Token Parser b -> ParseLocation -> Text -> Either String (b, ValueStore)
runTokenParse = lowLevelRunParse evalTokenIndentationParserT

forceDeclarations :: Text -> ([Decl Text], ValueStore)
forceDeclarations str = case runTokenParse parseDecls forceLocation str of
  Left bad -> error bad
  Right result -> result

forceTm :: Text -> (Tm', ValueStore)
forceTm str = case runTokenParse parseTm forceLocation str of
  Left bad -> error bad
  Right result -> result
