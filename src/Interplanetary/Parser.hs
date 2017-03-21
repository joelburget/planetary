{-# LANGUAGE PackageImports, ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}
-- A simple Core Frank parser based on the frankjnr implementation
module Interplanetary.Parser where

import Control.Applicative
import Control.Monad
import Control.Monad.IO.Class

import Text.Trifecta
import "indentation-trifecta" Text.Trifecta.Indentation

import Data.Char
import Data.IntMap.Lazy (IntMap)
import qualified Data.IntMap as IntMap

import Text.Parser.Token as Tok
import Text.Parser.Token.Style
import qualified Text.Parser.Token.Highlight as Hi
import qualified Data.HashSet as HashSet

import Interplanetary.Syntax

newtype CoreParser t m a =
  CoreParser { runCoreParser :: IndentationParserT t m a }
  deriving (Functor, Alternative, Applicative, Monad, Parsing
           , IndentationParsing)

deriving instance (DeltaParsing m) => (CharParsing (CoreParser Char m))
deriving instance (DeltaParsing m) => (CharParsing (CoreParser Token m))
deriving instance (DeltaParsing m) => (TokenParsing (CoreParser Char m))

instance DeltaParsing m => TokenParsing (CoreParser Token m) where
  someSpace = CoreParser $ buildSomeSpaceParser someSpace haskellCommentStyle
  nesting = CoreParser . nesting . runCoreParser
  semi = CoreParser $ runCoreParser semi
  highlight h = CoreParser . highlight h . runCoreParser
  token p = (CoreParser $ token (runCoreParser p)) <* whiteSpace

type MonadicParsing m = (TokenParsing m, IndentationParsing m, Monad m)

frankStyle :: MonadicParsing m => IdentifierStyle m
frankStyle = IdentifierStyle {
    _styleName = "Frank"
  , _styleStart = satisfy (\c -> isAlpha c || c == '_')
  , _styleLetter = satisfy (\c -> isAlphaNum c || c == '_' || c == '\'')
  , _styleReserved = HashSet.fromList ["data", "interface", "let", "letrec", "in"]
  , _styleHighlight = Hi.Identifier
  , _styleReservedHighlight = Hi.ReservedIdentifier }

arr, bar, assign, bang :: MonadicParsing m => m String
arr = symbol "->"
bar = symbol "|"
assign = symbol "="
bang = symbol "!"

reserved :: MonadicParsing m => String -> m ()
reserved = Tok.reserve frankStyle

identifier :: MonadicParsing m => m String
identifier = Tok.ident frankStyle

parseTyVar :: MonadicParsing m => m TyVar
parseTyVar = todo "parseTyVar"

parseValTy' :: MonadicParsing m => m ValTy
parseValTy' = -- parens parseValTy
          -- <|> SuspendedTy <$> try (braces parseCompTy)
          -- <|>
          VariableTy <$> parseTyVar

parseTyArg :: MonadicParsing m => m TyArg
parseTyArg = TyArgVal <$> parseValTy'
         -- <|> TyArgAbility <$> brackets parseAbilityBody

evalCharIndentationParserT
  :: Monad m => CoreParser Char m a -> IndentationState -> m a
evalCharIndentationParserT = evalIndentationParserT . runCoreParser

evalTokenIndentationParserT
  :: Monad m => CoreParser Token m a -> IndentationState -> m a
evalTokenIndentationParserT = evalIndentationParserT . runCoreParser

runParse :: (t -> IndentationState-> Parser b) -> t -> String -> Either String b
runParse ev p input
 = let indA = ev p $ mkIndentationState 0 infIndentation True Ge
   in case parseString indA mempty input of
    Failure err -> Left (show err)
    Success t -> Right t

--runCharParse = runParse evalCharIndentationParserT
runTokenParse :: CoreParser Token Parser b -> String -> Either String b
runTokenParse p = runParse evalTokenIndentationParserT p
