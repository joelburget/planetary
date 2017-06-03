{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language TypeApplications #-}
{-# language QuasiQuotes #-}
module Planetary.Library.FrankExamples where

import Control.Monad.Except
import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import qualified Data.Text as T
import System.IO (hFlush, stdout)
import Network.IPLD

import Planetary.Core
import Planetary.Library.HaskellForeign
import Planetary.Support.Parser.QQ
import Planetary.Support.Ids

-- Examples from the Frank paper.

-- We need some ffi definitions for working with chars / strings
--   (eraseCharLit, textMap, charHandler1, charHandler2)

eraseCharLit :: TmI
eraseCharLit = mkForeignTm @Text "\b \b"

-- TODO: we actually map with a data constructor
textMap :: SpineI -> ForeignM TmI
textMap [LambdaV _binderNames body, ForeignDataTm uid] = do
  text <- lookupForeign @Text uid
  let str = T.unpack text
  let fun :: Char -> ForeignM Char
      fun char = do
        charPtr <- ForeignDataTm <$> writeForeign char
        -- HACK XXX
        ouch [charPtr]
        pure char
  result <- T.pack <$> traverse fun str
  ForeignDataTm <$> writeForeign result
textMap _ = throwError FailedForeignFun

-- charHandler1 :: TmI -> ContinuationI -> Char -> TmI
charHandler1 :: SpineI -> ForeignM TmI
charHandler1 [b1, b2, ForeignDataTm uid] = do
  char <- lookupForeign uid
  pure $ case char of
    '\b' -> b1
    c -> Cut (Application [b2]) (mkForeignTm @Char c)
charHandler1 _ = throwError FailedForeignFun

-- charHandler2 :: TmI -> TmI -> TmI -> Char -> TmI
charHandler2 :: SpineI -> ForeignM TmI
charHandler2 [b1, b2, b3, ForeignDataTm uid] =
  flip fmap (lookupForeign uid) $ \case
    '0' -> b1
    ' ' -> b2
    _   -> b3
charHandler2 _ = throwError FailedForeignFun

inch :: SpineI -> ForeignM TmI
inch [] = do
  c <- liftIO getChar
  -- Taken from Shonky/Semantics
  let c' = if c == '\DEL' then '\b' else c
  ForeignDataTm <$> writeForeign c'
inch _ = throwError FailedForeignFun

ouch :: SpineI -> ForeignM TmI
ouch [ForeignDataTm uid] = do
  c <- lookupForeign uid
  liftIO $ putChar c >> hFlush stdout
  pure (DataTm unitId 0 [])
ouch _ = throwError FailedForeignFun

externals :: CurrentHandlers
externals = uIdMapFromList
  [ (consoleId, [ inch, ouch ])
  , (textId, [ textMap ])
  , (charHandlerId, [ charHandler1, charHandler2 ])
  ]

env :: EvalEnv
env =
  ( externals
  , uIdMapFromList
    [ mkForeign @Text "\b \b"
    ]
  )

-- runIt :: IO ()
-- runIt = print . fst =<< run env [] main

-- TODO:
-- * fix up textMap
-- * how is this actually run?

-- * inductive data

charId :: Cid
charId = undefined

-- [declarations|
-- data Zero = -- no constructors

-- data Unit =
--   <unit>

-- data Bool =
--   <tt>
--   | <ff>

-- data Pair X Y =
--   <pair X Y>

-- -- TODO: we can't do inductive data
-- -- data Nat =
-- --   | <zero>
-- --   | <suc Nat>

-- -- data List =
-- --   | <nil>
-- --   | <cons X (List X)>

-- interface Send X =
--   send : X -> <Unit>
-- interface Receive X =
--   receive : X
-- -- interface State X =
-- --   | get : S
-- --   | put : S -> Unit
-- interface Abort =
--   aborting : <Zero>

-- interface LookAhead =
--   peek : $charId
--   | accept : <Unit>

-- interface Console =
--   inch : $charId
--   | ouch : $charId -> <Unit>

-- -- XXX inductive
-- data Log [e] X =
--   <start {[e]X}>
--   | <inched <Log [e] X> {$charId -> [e]X}>
--   | <ouched <Log [e] X>>

-- data Buffer =
--   <empty>
--   | <hold $charId>

-- main = letrec
--   input : forall X. {<Log [<LookAhead>, <Abort>, <Console>] X>
--         -> Buffer
--         -> X
--         -> [Console]X}
--         = \log buffer x -> handle x : X with
--           LookAhead:
--             | <peek -> k> -> case buffer of
--               Buffer:
--                 | <hold c> -> input <Buffer.0 c> (k c)
--                 | <empty> -> on Console.0! (charHandler1
--                   (rollback l)                                  -- '\b'
--                   (\c -> input <Log.1 l k> <Buffer.0 c> (k c)) -- other char
--                   )
--             | <accept -> k> -> case buffer of
--               Buffer:
--                 | <hold c> -> snd (Console.1 c) (input <Log.2 l> empty (k unit))
--                 | <empty>  -> input l empty (k unit)
--           Abort:
--             | <aborting -> k> -> rollback log
--           | x -> x
--   .

--   rollback : forall X. {<Log [<LookAhead>, <Abort>, <Console>] X> -> [<Console>]X}
--            = \x -> case x of
--     Log:
--       | <start p> -> parse p
--       | <ouched l> -> snd (textMap Console.1 $eraseCharLit) (rollback l)
--       | <inched l k> -> input l empty (k LookAhead.0!)
--   .

--   parse : forall X. {{[<LookAhead>, <Abort>, <Console>]X} -> [<Console>]X}
--         = \p -> input <Log.0 p> empty p!
--   .

--   on : forall X Y. {X -> {X -> Y} -> Y}
--      = \x f -> f x
--   .

--   snd : forall X Y. {X -> Y -> X}
--       = \x y -> y
--   .

--   zeros : forall. {$Int -> [<LookAhead>, <Abort>]$Int}
--         = \n -> on LookAhead.0! (charHandler2
--       (snd LookAhead.1! (zeros ($add n 1))) -- '0'
--       (snd LookAhead.1! n)                  -- ' '
--       (abort!)                        -- other char
--     )
--   .

-- -- in (parse (zeros $zero) : [<Console>]$Int)
-- in parse (zeros $zero)

-- -- is this a module?
-- fns = letrec
--   fst : forall X Y. {X -> Y -> X}
--       = \x y -> x
--       .

--   if_ : forall X. {<Bool> -> {X} -> {X} -> X}
--       = \val t f -> case val of
--         Bool:
--           <tt> -> t!
--           <ff> -> f!
--         .

--   -- TODO: consider why Abort doesn't appear in the signature
--   -- catch : forall X. {<Abort>X -> {X} -> X}
--   catch : forall X. {X -> {X} -> X}
--         = \x h -> handle x : X with
--           Abort:
--             <aborting -> _> -> h! -- handle the abort

--           -- TODO: we require renaming the value here?
--           | x -> x -- it returned a value, pass on
--           .

-- in catch

-- -- TODO
-- -- * syntax for data constructors
-- -- * remove duplicate mention of adjustments / effects handled

-- -- pipe = letrec
-- --   pipe : forall [e] X Y. {{[e, Abort, Send X] Unit} -> [e, Abort, Receive X] Y} -> [e, Abort] Y}
-- --        -- TODO change the lambda delimiter from `->` to `.` like the paper?
-- --        = \x y -> handle y! : [e | <Abort>] Y with
-- --          Send X:
-- --            | x -> s -> handle y! : [e, Abort] Y with
-- --              Receive X:
-- --                | <receive -> r> -> pipe (s unit) (r x)
-- --              | y -> y
-- --          | x -> case x of
-- --            Unit:
-- --              | <unit> -> handle y! : [e, Abort] Y with
-- --                Receive X:
-- --                  | <aborting -> r> -> abort!
-- --                | y -> y
-- --        .
-- -- in pipe

-- |]
