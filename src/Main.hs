{-# language DataKinds #-}
{-# language OverloadedStrings #-}

module Main where

import Control.Lens
import Data.Aeson -- (encode, decode')
import Data.Monoid ((<>))
import qualified Data.HashMap.Lazy as HashMap
import Data.String (IsString)
import Network.Wreq
import qualified Data.ByteString.Lazy.Char8 as BS

import Tower.Genesis
import Tower.Eval

-- | An IPFS CID
newtype IpfsAddr = IpfsAddr String deriving (IsString)

getUrl, putUrl :: String
getUrl = "http://localhost:5001/api/v0/dag/get?arg="
putUrl = "http://localhost:5001/api/v0/dag/put"

putIpfs :: GenesisTerm -> IO ()
putIpfs tm = do
  let file = partLBS "file" (encode tm)
           & partContentType .~ Just "text/json"
  r <- post putUrl file
  print (r ^.. responseBody)

getIpfs :: IpfsAddr -> IO (Either String GenesisTerm)
getIpfs (IpfsAddr cid) = do
  r <- get (getUrl <> cid)
  BS.putStrLn (r ^. responseBody)
  pure $ eitherDecode' (r ^. responseBody)

-- Examples:

unit :: GenesisTerm
unit = Product' (NominalDomain HashMap.empty)

nothing :: GenesisValue 'Nominal 'Additive
nothing = Sum "nothing" unit

elimNothing :: GenesisCovalue 'Nominal 'Additive
elimNothing = Case $ NominalDomain $ HashMap.fromList [ ("nothing", unit) ]

comp :: GenesisTerm
comp = Computation nothing elimNothing

main :: IO ()
main = do
  print comp
  print (step comp)

  -- put it in, get it out
  putIpfs comp
  getIpfs "zdpuB22KVjXvFZpDxxP4XYQRX1Jnyq9oERNz46z4mEc5yAxoG"
