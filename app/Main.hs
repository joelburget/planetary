{-# language GeneralizedNewtypeDeriving #-}
{-# language OverloadedStrings #-}

module Main where

import Control.Lens
import Data.Aeson -- (encode, decode')
import Data.Monoid ((<>))
import qualified Data.HashMap.Lazy as HashMap
import Data.String (IsString)
import Network.Wreq
import qualified Data.ByteString.Lazy.Char8 as BS

import Interplanetary.Examples
import Interplanetary.Genesis
import Interplanetary.Typecheck
-- import Interplanetary.Eval
import Interplanetary.JSON ()
-- import Interplanetary.Oracles
-- import Interplanetary.StrNat

-- | An IPFS CID
newtype IpfsAddr = IpfsAddr String deriving (IsString)

getUrl, putUrl :: String
getUrl = "http://localhost:5001/api/v0/dag/get?arg="
putUrl = "http://localhost:5001/api/v0/dag/put"

{-
putIpfs :: Toplevel -> IO ()
putIpfs tm = do
  let file = partLBS "file" (encode tm)
           & partContentType .~ Just "text/json"
  r <- post putUrl file
  print (r ^.. responseBody)

getIpfs :: IpfsAddr -> IO (Either String Toplevel)
getIpfs (IpfsAddr cid) = do
  r <- get (getUrl <> cid)
  BS.putStrLn (r ^. responseBody)
  pure $ eitherDecode' (r ^. responseBody)
-}

-- Examples:
-- check :: Term -> Vector Type -> TypingContext ()
-- runTypingContext :: TypingContext a -> Either CheckFailure a

main :: IO ()
main = do
  -- TODO
  -- print $ runContext (HashMap.fromList []) (step comp')

  -- put it in, get it out
  -- putIpfs comp'
  -- comp'' <- getIpfs "zdpuB22KVjXvFZpDxxP4XYQRX1Jnyq9oERNz46z4mEc5yAxoG"
  -- print comp''

  print $ topCheck compT
