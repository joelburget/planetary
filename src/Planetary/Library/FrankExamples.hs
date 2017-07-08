{-# language LambdaCase #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
module Planetary.Library.FrankExamples (resolvedDecls) where

import Control.Monad.Except
import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import qualified Data.Text as T
import System.IO (hFlush, stdout)
import NeatInterpolation
import Network.IPLD

import Planetary.Core
import Planetary.Library.HaskellForeign
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser

-- Examples from the Frank paper.

-- We need some ffi definitions for working with chars / strings
--   (eraseCharLit, textMap, charHandler1, charHandler2)

eraseCharLit :: TmI
eraseCharLit = mkForeignTm @Text textId [] "\b \b"

-- TODO: we actually map with a data constructor
textMap :: SpineI -> ForeignM TmI
textMap [Lambda _binderNames body, ForeignValue _ _ uid] = do
  fText <- lookupForeign uid
  let str = T.unpack fText
  let fun :: Char -> ForeignM Char
      fun char = do
        charPtr <- ForeignValue charId [] <$> writeForeign char
        -- HACK XXX
        ouch [charPtr]
        pure char
  result <- T.pack <$> traverse fun str
  ForeignValue textId [] <$> writeForeign result
textMap _ = throwError FailedForeignFun

-- charHandler1 :: TmI -> ContinuationI -> Char -> TmI
charHandler1 :: SpineI -> ForeignM TmI
charHandler1 [b1, b2, ForeignValue _ _ uid] = do
  char <- lookupForeign uid
  pure $ case char of
    '\b' -> b1
    c -> Cut (Application [b2]) (mkForeignTm @Char charId [] c)
charHandler1 _ = throwError FailedForeignFun

-- charHandler2 :: TmI -> TmI -> TmI -> Char -> TmI
charHandler2 :: SpineI -> ForeignM TmI
charHandler2 [b1, b2, b3, ForeignValue _ _ uid] =
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
  ForeignValue charId [] <$> writeForeign c'
inch _ = throwError FailedForeignFun

ouch :: SpineI -> ForeignM TmI
ouch [ForeignValue _ _ uid] = do
  c <- lookupForeign uid
  liftIO $ putChar c >> hFlush stdout
  pure (DataConstructor unitId 0 [])
ouch _ = throwError FailedForeignFun

externals :: CurrentHandlers
externals =
  [ (consoleId, [ inch, ouch ])
  , (textId, [ textMap ])
  , (charHandlerId, [ charHandler1, charHandler2 ])
  ]

env :: EvalEnv
env = EvalEnv
  externals
  [ mkForeign @Text "\b \b"
  ]

-- runIt :: IO ()
-- runIt = print . fst =<< run env [] main

-- TODO:
-- * fix up textMap
-- * how is this actually run?

decls :: [DeclS]
decls = forceDeclarations [text|
data Zero = -- no constructors

data Unit =
  | <unit>

data Bool =
  | <ff>
  | <tt>

data Pair X Y =
  | <pair X Y>

-- TODO NatF is duplicated in Eval.Test
data NatF Nat =
  | <zero>
  | <suc Nat>

-- TODO ListF is duplicated in HaskellForeign.Test
data ListF X list =
  | <nil>
  | <cons X <list X>>

interface Send X =
  | send : X -> <Unit>

interface Receive X =
  | receive : X

-- interface State X =
--   | get : S
--   | put : S -> Unit

interface Abort =
  | aborting : <Zero>

interface LookAhead =
  | peek : char
  | accept : <Unit>

interface Console =
  | inch : char
  | ouch : char -> <Unit>

-- XXX inductive
data LogF [e] X Log =
  | <start {[e]X}>
  | <inched <Log [e] X> {char -> [e]X}>
  | <ouched <Log [e] X>>

data Buffer =
  | <empty>
  | <hold char>

main = letrec
  input : forall X. {<Log [<LookAhead>, <Abort>, <Console>] X>
        -> Buffer
        -> X
        -> [Console]X}
        = \log buffer x -> handle x : X with
          LookAhead:
            | <peek -> k> -> case buffer of
              Buffer:
                | <hold c> -> input <Buffer.0 c> (k c)
                | <empty> -> on Console.0! (charHandler1
                  (rollback l)                                  -- '\b'
                  (\c -> input <Log.1 l k> <Buffer.0 c> (k c)) -- other char
                  )
            | <accept -> k> -> case buffer of
              Buffer:
                | <hold c> -> snd (Console.1 c) (input <Log.2 l> empty (k unit))
                | <empty>  -> input l empty (k unit)
          Abort:
            | <aborting -> k> -> rollback log
          | x -> x

  rollback : forall X. {<Log [<LookAhead>, <Abort>, <Console>] X> -> [<Console>]X}
           = \x -> case x of
    Log:
      | <start p> -> parse p
      | <ouched l> -> snd (textMap Console.1 eraseCharLit) (rollback l)
      | <inched l k> -> input l empty (k LookAhead.0!)

  parse : forall X. {{[<LookAhead>, <Abort>, <Console>]X} -> [<Console>]X}
        = \p -> input <Log.0 p> empty p!

  on : forall X Y. {X -> {X -> Y} -> Y}
     = \x f -> f x

  snd : forall X Y. {X -> Y -> X}
      = \x y -> y

  zeros : forall. {Int -> [<LookAhead>, <Abort>]Int}
        = \n -> on LookAhead.0! (charHandler2
          (snd LookAhead.1! (zeros (add n 1))) -- '0'
          (snd LookAhead.1! n)                 -- ' '
          (abort!)                             -- other char
        )

-- in (parse (zeros zero) : [<Console>]Int)
in parse (zeros zero)

-- is this a module?
fns = letrec
  fst : forall X Y. {X -> Y -> X}
      = \x y -> x

  if_ : forall X. {<Bool> -> {X} -> {X} -> X}
      = \val t f -> case val of
        Bool:
          | <tt> -> t!
          | <ff> -> f!

  -- TODO: consider why Abort doesn't appear in the signature
  -- catch : forall X. {<Abort>X -> {X} -> X}
  catch : forall X. {X -> {X} -> X}
        = \x h -> handle x : X with
          Abort:
            | <aborting -> _> -> h! -- handle the abort

          -- TODO: we require renaming the value here?
          | x -> x -- it returned a value, pass on

in catch

pipe = letrec
  pipe : forall [e] X Y. {
         {{[e, <Abort>, <Send X>] Unit} -> [e, <Abort>, <Receive X>] Y}
       -> [e, <Abort>] Y}
       -- TODO change the lambda delimiter from `->` to `.` like the paper?
       = \x y -> handle y! : [e, <Abort>] Y with
         Send X:
           | <send x -> s> -> handle y! : [e, <Abort>] Y with
             Receive X:
               | <receive -> r> -> pipe (s unit) (r x)
             | y -> y
         | x -> case x of
           Unit:
             | <unit> -> handle y! : [e, <Abort>] Y with
               Receive X:
                 | <aborting -> r> -> abort!
               | y -> y
in pipe
|]

-- TODO
charId, eraseCharLitId, addId, zeroId :: Cid
charId = mkCid "TODO charId"
eraseCharLitId = mkCid "TODO eraseCharLitId"
addId = mkCid "TODO addId"
zeroId = mkCid "TODO zeroId"

predefined :: UIdMap Text Cid
predefined =
  [ ("char", charId)
  , ("eraseCharLit", eraseCharLitId)
  , ("Int", intId)
  , ("add", addId)
  , ("zero", zeroId)
  ]

resolvedDecls :: ResolvedDecls
Right resolvedDecls = resolveDecls decls predefined
