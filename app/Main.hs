{-# LANGUAGE OverloadedStrings #-}

module Main where

import Data.ByteString (ByteString)
import Control.Monad (forever)
import qualified Network.WebSockets as WS

type Client = WS.Connection

application :: WS.ServerApp
application pending = do
  conn <- WS.acceptRequest pending
  WS.forkPingThread conn 30
  talk conn

talk :: WS.Connection -> IO ()
talk conn = forever $ do
  -- echo
  msg <- WS.receiveData conn
  WS.sendTextData conn (msg :: ByteString)

main :: IO ()
main = WS.runServer "0.0.0.0" 9160 application
