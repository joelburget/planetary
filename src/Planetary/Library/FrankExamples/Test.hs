{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Library.FrankExamples.Test (unitTests) where

import Control.Lens
import Data.Text (Text)
import NeatInterpolation
import Test.Tasty

import Planetary.Core
import qualified Planetary.Library.FrankExamples as Frank
import Planetary.Core.Eval.Test (runTest)
import Planetary.Library.HaskellForeign (mkForeignTm)
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser

unitTests :: TestTree
unitTests =
  let
  in testGroup "frank examples"
       [ testGroup "catch" []
       , testGroup "pipe" []
       , testGroup "spacer" []
       , testGroup "state" []
       , testGroup "next"
         [ let
               emptyEnv :: AmbientEnv
               emptyEnv = AmbientEnv mempty mempty

               next = forceTm [text|
                 test = letrec
                   next : [State Int]Int
                   next! = fst get! (put (add get! zero))

                   index : <List X> -> <List <Pair Int X>>
                         = \xs -> state zero (map {\x -> pair next! x} xs)

                   actual = index abc
                   expected = cons (pair zero a)
                     (cons (pair one b)
                       (cons (pair two c) nil))
               |]

               add = Command intOpsId 0
               abc = mkForeignTm @Text textId [] "abc"

               zero = mkForeignTm @Int intId [] 0
               one = mkForeignTm @Int intId [] 1
               two = mkForeignTm @Int intId [] 2

               a = mkForeignTm @Text textId [] "a"
               b = mkForeignTm @Text textId [] "b"
               c = mkForeignTm @Text textId [] "c"

               resolutionState = fromList $
                 -- Provides State, List, Pair
                 (Frank.resolvedDecls ^. globalCids) ++
                 [("Int", intId)]

               Right next' = resolveTm resolutionState next
               Right next'' = closeTm $
                 substituteAll
                   [ ("add", add)
                   , ("abc", abc)
                   , ("zero", zero)
                   , ("one", one)
                   , ("two", two)
                   , ("a", a)
                   , ("b", b)
                   , ("c", c)
                   ]
                   next'

               state = forceTm [text|
                 state = letrec
                   state : forall S X. S -> <State S>X -> X
                         = \s x -> handle x : X with
                           State:
                             | <get -> k> -> state s (k s)
                             | <put s -> k> -> state s (k <Unit.0>)
                           | x -> x
               |]

               Right state' = resolveTm resolutionState state
               Right state'' = closeTm state'
            in runTest "next one" emptyEnv next'' (Right one)
         ]

       -- Example from "Continuation Passing Style for Effect Handlers"
       -- - Hillerström, Lindley, Atkey, Sivaramakrishnan
       , let tm = forceTm [text|
             drunkToss : [<Choose <Bool>>, <Abort>] Toss
                       -- decide whether the coin is caught
                       = ifthenelse (Choose.0!)
                           -- decide the face
                           (ifthenelse (Choose.0!) Toss.0 Toss.1)
                           (Abort.0!)

             -- use a list to model nondeterminism
             nondet : forall A. [<Choose <Bool>>, <Abort>] A -> <List A>
                    = \a -> handle a with
                      Choose:
                        | <choose -> k> -> concat (k Bool.0) (k Bool.1)
                      Abort:
                        | <aborting -> k> -> emptyList
                      | x -> singletonList x

             -- TODO:
             --   * should p come first or last?
             --   * can we use variables other than e yet?
             --   * is this the correct way to handle a value?
             --   * change declarations format:
             --     - data and effects aren't really different?
             --     - toplevel letrec is weird - instead make it implicit
             --   * nits
             --     - really would be nice to remove some angle brackets
             --     - s/True/Bool.0
             allChoices : forall A. [p, <Choose <Bool>>] A -> [p] <List <A>>
                        = \a -> handle a : A with
                          Choose:
                            | <choose -> k> -> concat (k Bool.0) (k Bool.1)
                          | x -> singletonList x

             failure : forall A. [p, <Abort>] -> [p] <List <A>>
                     = \a -> handle a : A with
                       Abort
                         | <aborting -> k> -> emptyList
                       | x -> singletonList x

             -- should give []
             composition1 : forall A. [<Choose <Bool>>, <Abort>] A -> <List A>
                          = \a -> failure (allChoices a)

             -- should give [[Heads], [Tails], []]
             composition2 : forall A. [<Choose <Bool>>, <Abort>] A -> <List A>
                          = \a -> allChoices (failure a)
             |]
           in runTest "drunk toss" undefined undefined undefined
       ]
