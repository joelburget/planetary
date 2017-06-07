{-# language LambdaCase #-}
{-# language TemplateHaskellQuotes #-}
{-# language TemplateHaskell #-}
{-# language ViewPatterns #-}
module Planetary.Support.Parser.QQ where

import Control.Arrow ((>>>))
import Control.Lens (minimumOf)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B8
import Data.Char (isSpace)
import Data.Generics.Aliases
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as T
import Data.Typeable (Typeable)
import Language.Haskell.TH
  (ExpQ, Exp(..), Lit(..), appE, varE, litE, mkName, lookupValueName)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

import Planetary.Support.Parser

-- TODO:
-- * type quoter
-- * location info

tmExp :: QuasiQuoter
tmExp = QuasiQuoter
  { quoteExp  = quoteTmExp
  , quotePat  = const (fail "can't quote tm patterns")
  , quoteType = const (fail "can't quote tm types")
  , quoteDec  = const (fail "can't quote tm declarations")
  }

parseLocation :: TH.Loc -> ParseLocation
parseLocation loc =
  let filename = TH.loc_filename loc
      line = fst (TH.loc_start loc)
  in ParseLocation (B8.pack filename) (fromIntegral line) 0

quoteTmExp :: String -> ExpQ
quoteTmExp str = do
  loc <- TH.location
  let str' = normalizeQQInput str
      pos = parseLocation loc
  case runTokenParse parseTm pos (T.pack str') of
    Left err -> fail ("failed to parse tm: " ++ err)
    Right parsedTm -> dataToExpQ handleAll parsedTm

declarations :: QuasiQuoter
declarations = QuasiQuoter
  { quoteExp  = quoteDeclarations
  , quotePat  = const (fail "can't quote declarations patterns")
  , quoteType = const (fail "can't quote declarations types")
  , quoteDec  = const (fail "can't quote declarations")
  }

quoteDeclarations :: String -> ExpQ
quoteDeclarations str = do
  loc <- TH.location
  let str' = normalizeQQInput str
      pos = parseLocation loc
  case runTokenParse parseDecls pos (T.pack str') of
    Left err -> fail ("failed to parse declarations: " ++ err)
    Right decls -> dataToExpQ handleAll decls

handleAll :: Typeable a => a -> Maybe ExpQ
handleAll = const Nothing `extQ` handleByteString `extQ` handleText

-- https://stackoverflow.com/questions/12788181/data-text-text-and-quasiquoting
handleByteString :: ByteString -> Maybe ExpQ
handleByteString x =
  -- convert the ByteString to a string literal
  -- and wrap it with B8.pack
  Just $ appE (varE 'B8.pack) $ litE $ StringL $ B8.unpack x

handleText :: Text -> Maybe ExpQ
handleText x =
  -- convert the text to a string literal
  -- and wrap it with T.pack
  Just $ appE (varE 'T.pack) $ litE $ StringL $ T.unpack x

-- Adapted from https://github.com/nikita-volkov/neat-interpolation/blob/master/library/NeatInterpolation/String.hs:

normalizeQQInput :: String -> String
normalizeQQInput = trim . unindent . lines . tabsToSpaces
  where
    unindent :: [String] -> String
    unindent = \case
      l:ls ->
        let
          unindentedHead = dropWhile (== ' ') l
          indent = minimumIndent ls
          unindentedTail = map (drop indent) ls
        in unlines $ unindentedHead : unindentedTail
      [] -> []

trim :: String -> String
trim = dropWhileRev isSpace . dropWhile isSpace

dropWhileRev :: (a -> Bool) -> [a] -> [a]
dropWhileRev p = foldr (\x xs -> if p x && null xs then [] else x:xs) []

tabsToSpaces :: String -> String
tabsToSpaces ('\t':cs) = "    " ++ tabsToSpaces cs
tabsToSpaces (c   :cs) = c       : tabsToSpaces cs
tabsToSpaces [] = []

minimumIndent :: [String] -> Int
minimumIndent =
      filter (not . null . dropWhile isSpace)
  >>> map lineIndent
  >>> minimumOf traverse
  >>> fromMaybe 0

-- | Amount of preceding spaces on first line
lineIndent :: String -> Int
lineIndent = length . takeWhile (== ' ')
