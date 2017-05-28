{-# language QuasiQuotes #-}
module Planetary.Library.Frank where

import Planetary.Support.Parser.QQ

-- ~A demonstration of building Frank on top of core frank.~
--
-- Examples from the Frank paper.

[declarations|
data Zero = -- no constructors

data Unit =
  | -- unit

data Bool =
  | -- tt
  | -- ff

data Pair X Y =
  | X Y -- pair

-- TODO: we can't do inductive data
-- data Nat =
--   | -- zero
--   | Nat -- suc

-- data List =
--   | -- nil
--   | X (List X) -- cons

interface Send X = X -> <Unit> -- send
interface Receive X = X -- receive
-- interface State X =
--   | S -- get
--   | S -> Unit -- put
interface Abort = <Zero> -- aborting

-- is this a module?
fns = letrec
  fst : forall X Y. {X -> Y -> X}
      = \x y -> x
      .

  snd : forall X Y. {X -> Y -> X}
      = \x y -> y
      .

  on : forall X Y. {X -> {X -> Y} -> Y}
     = \x f -> f x
     .

  if_ : forall X. {<Bool> -> {X} -> {X} -> X}
      = \val t f -> case val of
        Bool:
        | -> t!
        | -> f!
        .

  -- TODO: consider why Abort doesn't appear in the signature
  -- catch : forall X. {<Abort>X -> {X} -> X}
  catch : forall X. {X -> {X} -> X}
        = \x h -> handle x : X with
          Abort:
            | -> aborting -> h! -- handle the abort
          -- TODO: we require renaming the value here?
          | x -> x -- it returned a value, pass on
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
