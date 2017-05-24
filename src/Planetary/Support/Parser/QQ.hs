{-# language LambdaCase #-}
{-# language TemplateHaskellQuotes #-}
module Planetary.Support.Parser.QQ where

import Control.Arrow ((>>>))
import Control.Lens (minimumOf)
import Control.Monad (join)
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as B8
import Data.Char (isSpace)
import Data.Generics.Aliases
import Data.Maybe (fromMaybe)
import Language.Haskell.TH
  (ExpQ, DecsQ, Exp(..), Lit(..), appE, varE, litE, mkName)
import qualified Language.Haskell.TH as TH
import Language.Haskell.TH.Quote
import Language.Haskell.TH.Syntax (Dec(..), Pat(..), Body(..), Type(ConT))
import Network.IPLD (Cid)

import Planetary.Core
import Planetary.Support.MakeTables
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
  case runTokenParse parseTm pos str' of
    Left err -> fail ("failed to parse tm: " ++ err)
    Right parsedTm -> dataToExpQ
      (const Nothing `extQ` antiTmExp `extQ` handleByteString)
      parsedTm

antiTmExp :: Tm' -> Maybe ExpQ
antiTmExp  (V ('$':name)) = Just $ pure $ VarE $ mkName name
antiTmExp  _              = Nothing

antiTyExp :: ValTy' -> Maybe ExpQ
antiTyExp  (VariableTy ('$':name)) = Just $ pure $ VarE $ mkName name
antiTyExp  _                       = Nothing

declarations :: QuasiQuoter
declarations = QuasiQuoter
  { quoteExp  = quoteDeclarations
  , quotePat  = const (fail "can't quote declarations patterns")
  , quoteType = const (fail "can't quote declarations types")
  , quoteDec  = quoteDeclarationsDec
  }

-- TODO: this doesn't seem very useful
quoteDeclarations :: String -> ExpQ
quoteDeclarations str = do
  loc <- TH.location
  let str' = normalizeQQInput str
      pos = parseLocation loc
  case runTokenParse parseDecls pos str' of
    Left err -> fail ("failed to parse declarations: " ++ err)
    Right decls -> case makeTables decls of
      Left err -> fail ("failed to make tables: " ++ show err)
      Right tables -> dataToExpQ
        (const Nothing `extQ` antiTmExp `extQ` handleByteString)
        tables

quoteDeclarationsDec :: String -> DecsQ
quoteDeclarationsDec str = do
  loc <- TH.location
  let str' = normalizeQQInput str
      pos = parseLocation loc
  case runTokenParse parseDecls pos str' of
    Left err -> fail ("failed to parse declarations: " ++ err)
    Right decls -> case makeTables decls of
      Left err -> fail ("failed to make tables: " ++ show err)
      Right (_dataTables, _interfaceTables, cids, tmDecls) -> do
        thDecls <- mapM thTmDecl tmDecls
        cidDecls <- mapM thCid cids
        pure (join thDecls ++ join cidDecls)

        -- TODO: we want to make the actual declarations available
        --
        -- mapM thDataDecl dataTables
        -- mapM thInterfaceDecl interfaceTables

thCid :: (String, Cid) -> DecsQ
thCid (name, cid) = do
  cid' <- dataToExpQ (const Nothing `extQ` handleByteString) cid
  let name' = mkName ("cid" ++ name)

  pure
    [ SigD name' (ConT ''Cid)
    , ValD (VarP name') (NormalB cid') []
    ]

thTmDecl :: Executable2 TermDecl -> DecsQ
thTmDecl (TermDecl name tm) = do
  tm' <- dataToExpQ
    (const Nothing `extQ` antiTmExp `extQ` handleByteString)
    tm
  let tmName = mkName name

  -- TODO: antiTyExp requires ValTy' but we have a ValTyI
  -- ty' <- dataToExpQ
  --   -- (const Nothing `extQ` antiTyExp `extQ` handleByteString)
  --   (const Nothing `extQ` handleByteString)
  --   ty
  -- let tyName = mkName (name ++ "Ty")

  pure
    [ SigD tmName (ConT ''TmI)
    , ValD (VarP tmName) (NormalB tm') []
    -- , SigD tyName (ConT ''(Scope ... ValTyI))
    -- , ValD (VarP tyName) (NormalB ty') []
    ]

-- https://stackoverflow.com/questions/12788181/data-text-text-and-quasiquoting
handleByteString :: ByteString -> Maybe ExpQ
handleByteString x =
    -- convert the ByteString to a string literal
    -- and wrap it with B8.pack
    Just $ appE (varE 'B8.pack) $ litE $ StringL $ B8.unpack x

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
