module Interplanetary.Parser.QQ where

import Data.Char (isSpace)
import Data.List (sort)
import Data.Maybe (listToMaybe)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote

import Interplanetary.MakeTables
import Interplanetary.Parser
import Interplanetary.Syntax

-- TODO:
-- * data / interface declaration quoter
-- * type quoter
-- * antiquotation
--   - we'd have to extend the syntax :/
-- * location info

tmExp :: QuasiQuoter
tmExp = QuasiQuoter
  { quoteExp  = quoteTmExp
  , quotePat  = const (fail "can't quote tm patterns")
  , quoteType = const (fail "can't quote tm types")
  , quoteDec  = const (fail "can't quote tm declarations")
  }

declarations :: QuasiQuoter
declarations = QuasiQuoter
  { quoteExp  = quoteDeclarations
  , quotePat  = const (fail "can't quote declarations patterns")
  , quoteType = const (fail "can't quote declarations types")
  , quoteDec  = const (fail "can't quote declarations declarations")
  }

quoteDeclarations :: String -> TH.ExpQ
quoteDeclarations str = do
  let str' = normalizeQQInput str
  case runTokenParse parseDataOrInterfaceDecls str' of
    Left err -> fail ("failed to parse declarations: " ++ err)
    Right decls -> case makeTables decls of
      Left err -> fail ("failed to make tables: " ++ show err)
      Right tables -> dataToExpQ (const Nothing) tables

quoteTmExp :: String -> TH.ExpQ
quoteTmExp str = do
  -- loc <- TH.location
  let str' = normalizeQQInput str
      -- (linePos, charPos) = TH.loc_start loc
      -- pos = (TH.loc_filename loc, linePos, charPos)
  -- tm <- parseTm pos str'
  case runTokenParse parseTm str' of
    Left err -> fail ("failed to parse tm: " ++ err)
    -- Just tm -> dataToExpQ (const Nothing `extQ` antiTmExp) tm
    Right parsedTm -> dataToExpQ (const Nothing) parsedTm

antiTmExp :: TmI -> Maybe (TH.Q TH.Exp)
-- antiTmExp  (AntiIntTm v)  = Just $ TH.appE  (TH.conE (TH.mkName "IntTm"))
--                                             (TH.varE (TH.mkName v))
-- antiTmExp  (AntiTm v)     = Just $ TH.varE  (TH.mkName v)
antiTmExp  _              = Nothing


-- Taken from https://github.com/nikita-volkov/neat-interpolation/blob/master/library/NeatInterpolation/String.hs:

normalizeQQInput :: String -> String
normalizeQQInput = trim . unindent' . tabsToSpaces
  where
    unindent' :: String -> String
    unindent' s =
      case lines s of
        l:ls ->
          let
            unindentedHead = dropWhile (== ' ') l
            minimumTailIndent = minimumIndent . unlines $ ls
            unindentedTail = case minimumTailIndent of
              Just indent -> map (drop indent) ls
              Nothing -> ls
          in unlines $ unindentedHead : unindentedTail
        [] -> []

trim :: String -> String
trim = dropWhileRev isSpace . dropWhile isSpace

dropWhileRev :: (a -> Bool) -> [a] -> [a]
dropWhileRev p = foldr (\x xs -> if p x && null xs then [] else x:xs) []

unindent :: String -> String
unindent s =
  case minimumIndent s of
    Just indent -> unlines . map (drop indent) . lines $ s
    Nothing -> s

tabsToSpaces :: String -> String
tabsToSpaces ('\t':cs) = "    " ++ tabsToSpaces cs
tabsToSpaces (c   :cs) = c       : tabsToSpaces cs
tabsToSpaces [] = []

minimumIndent :: String -> Maybe Int
minimumIndent =
  listToMaybe . sort . map lineIndent
    . filter (not . null . dropWhile isSpace) . lines

-- | Amount of preceding spaces on first line
lineIndent :: String -> Int
lineIndent = length . takeWhile (== ' ')
