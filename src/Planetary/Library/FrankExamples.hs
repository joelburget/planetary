{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
{-# language TypeApplications #-}
{-# language QuasiQuotes #-}
module Planetary.Library.FrankExamples where

import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import qualified Data.Text as T
import Network.IPLD
import System.IO (hFlush, stdout)

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
  text <- lookupForeign uid
  -- char -> ForeignM char
  result <- traverse _ text
  ForeignDataTm <$> writeForeign result

-- charHandler1 :: TmI -> ContinuationI -> Char -> TmI
charHandler1 :: SpineI -> ForeignM TmI
charHandler1 [b1, b2, ForeignDataTm uid] = do
  char <- lookupForeign uid
  pure $ case char of
    '\b' -> b1
    c -> Cut (Application [b2]) (mkForeignTm @Char c)

-- charHandler2 :: TmI -> TmI -> TmI -> Char -> TmI
charHandler2 :: SpineI -> ForeignM TmI
charHandler2 [b1, b2, b3, ForeignDataTm uid] = do
  flip fmap (lookupForeign uid) $ \case
    '0' -> b1
    ' ' -> b2
    _   -> b3

inch :: SpineI -> ForeignM TmI
inch [] = do
  c <- liftIO getChar
  -- Taken from Shonky/Semantics
  let c' = if c == '\DEL' then '\b' else c
  ForeignDataTm <$> writeForeign c'

ouch :: SpineI -> ForeignM TmI
ouch [ForeignDataTm uid] = do
  c <- lookupForeign uid
  liftIO $ putChar c >> hFlush stdout

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

-- TODO:
-- x clarify ffi (eraseCharLit, textMap, charHandler1, charHandler2)
-- x textMap
-- x understand commands vs functions
-- x fix up parser
-- * how is this actually run?

-- * inductive data

[declarations|
data Zero = -- no constructors

data Unit =
  | <unit>

data Bool =
  | <tt>
  | <ff>

data Pair X Y =
  | <pair X Y>

-- TODO: we can't do inductive data
-- data Nat =
--   | -- zero
--   | Nat -- suc

-- data List =
--   | <nil>
--   | <cons X (List X)>

interface Send X = X -> <Unit> -- send
interface Receive X = X -- receive
-- interface State X =
--   | S -- get
--   | S -> Unit -- put
interface Abort = <Zero> -- aborting

interface LookAhead =
  | peek : Char
  | accept : Unit

interface Console =
  | inch : Char
  | ouch : Char -> Unit

data Log [e] X =
  | <start {[e]X}>
  | <inched (Log [e] X) {Char -> [e]X}>
  | <ouched (Log [e] X)>

data Buffer =
  | <empty>
  | <hold Char>

main = letrec
  input : forall X. Log [LookAhead, Abort, Console] X
        -> Buffer
        -> <LookAhead, Abort>X
        -> [Console]X
        = \log buffer x -> handle x : X with
          LookAhead:
            <peek -> k> -> case buffer of
              Buffer:
                <hold c> -> input <hold c> (k c)
                <empty> -> on inch! (charHandler1
                  (rollback l)                              -- '\b'
                  (\c -> input (inched l k) (hold c) (k c)) -- other char
                  )
            <accept -> k> -> case buffer of
              Buffer:
                <hold c> -> snd (ouch c) (input (ouched l) empty (k unit))
                <empty>  -> input l empty (k unit)
          Abort:
            <aborting -> k> -> rollback log
          x -> x

  rollback : forall X. Log [LookAhead, Abort, Console] X -> [Console]X
  rollback = \x -> case x of
    <start p> -> parse p
    <ouched l> -> snd (textMap ouch $eraseCharLit) (rollback l)
    <inched l k> -> input l empty (k peek!)

  parse : {[LookAhead, Abort, Console]X} -> [Console]X
  parse = \p -> input (start p) empty p!

  zeros : Int -> [LookAhead, Abort]Int
  zeros n = on peek! (charHandler2
      (snd (accept!) (zeros (n + 1))) -- '0'
      (snd (accept!) n)               -- ' '
      (abort!)                        -- other char
    )

  -- map : forall X Y. {X -> Y} -> List X -> List Y
  -- map = \x y -> case y of
  --   List:
  --     | <nil>       -> <List.nil>
  --     | <cons x xs> -> <List.cons (f x) (map f xs>

  snd : forall X Y. {X -> Y -> X}
      = \x y -> y
      .

  on : forall X Y. {X -> {X -> Y} -> Y}
     = \x f -> f x
     .

in (parse (zeros 0) : [Console]Int)

-- is this a module?
fns = letrec
  fst : forall X Y. {X -> Y -> X}
      = \x y -> x
      .

  if_ : forall X. {<Bool> -> {X} -> {X} -> X}
      = \val t f -> case val of
        Bool:
          <tt> -> t!
          <ff> -> f!
        .

  -- TODO: consider why Abort doesn't appear in the signature
  -- catch : forall X. {<Abort>X -> {X} -> X}
  catch : forall X. {X -> {X} -> X}
        = \x h -> handle x : X with
          Abort:
            <aborting -> _> -> h! -- handle the abort

          -- TODO: we require renaming the value here?
          x -> x -- it returned a value, pass on
          .

in catch

-- TODO
-- * syntax for data constructors
-- * remove duplicate mention of adjustments / effects handled

-- pipe = letrec
--   pipe : forall [e] X Y. {{[e, Abort, Send X] Unit} -> [e, Abort, Receive X] Y} -> [e, Abort] Y}
--        -- TODO change the lambda delimiter from `->` to `.` like the paper?
--        = \x y -> handle y! : [e | <Abort>] Y with
--          Send X:
--            | x -> s -> handle y! : [e, Abort] Y with
--              Receive X:
--                | -> r -> pipe (s unit) (r x)
--              | y      -> y
--          | x -> case x of
--            Unit:
--              | unit -> handle y! : [e, Abort] Y with
--                Receive X:
--                  | -> r -> abort!
--                | y      -> y
--        .
-- in pipe

|]
