{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Library.FrankExamples.Test (unitTests) where

import Control.Exception (Exception, throw)
import Control.Lens
import Control.Monad.Except
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import Data.Text.Prettyprint.Doc
import Data.Typeable (Typeable)
import NeatInterpolation
import Network.IPLD (toIpld)
import EasyTest hiding (run)

import Planetary.Core
import qualified Planetary.Library.FrankExamples as Frank
import Planetary.Core.Eval.Test (runTest)
import Planetary.Library.HaskellForeign (mkForeignTm, intOpsId, haskellOracles)
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser

data NotEqual = NotEqual TmI TmI
  deriving (Show, Typeable)

instance Exception NotEqual

unitTests :: Test ()
unitTests = do
  Right testingDecls <- pure $ resolveDecls [ ("Unit", unitId) ] $
    forceDeclarations [text|
      interface TestingOps A B =
        | checkEqual : A -> B -> <Unit>
    |]

  Just (checkingOpsId, _) <- pure $ namedInterface "TestingOps" testingDecls

  let
      unit = DataConstructor unitId 0 []

      -- This should check that the two terms are equal. If so it just exits
      -- with unit, otherwise it throws (to easytest).
      checkEqualImpl :: Handler
      checkEqualImpl st
        | AppN _ [tm1, tm2] <- st ^. evalFocus =
          if tm1 == tm2
             then pure $ st & evalFocus .~ Value unit
             else throw $ NotEqual tm1 tm2
      checkEqualImpl _ = throwError (FailedForeignFun "checkEqualImpl")

      testingHandlers :: AmbientHandlers
      testingHandlers = AmbientHandlers $
        haskellOracles <>
        [ (checkingOpsId, [ checkEqualImpl ]) ]

      checkEqual = Command checkingOpsId 0

  scope "frank examples" $ tests
       [ scope "catch" $ tests []
       , scope "pipe" $ tests []
       , scope "spacer" $ tests []
       , scope "state" $ tests []
       , scope "next" $ tests
         [ do
              -- Just (listfId, _) <- pure $ namedData "ListF" Frank.resolvedDecls
              -- Just (pairId,  _) <- pure $ namedData "Pair"  Frank.resolvedDecls
              Just stateCid <- pure $
                Frank.resolvedDecls ^?  globalCids . to HashMap.fromList . ix "State"
              let
               test = forceTm [text|
                 letrec
                   -- note: not `forall S X. {S -> <State S>X -> X}`
                   state : forall S X. {S -> {X} -> X}
                         = \s x -> handle x! : X with
                           State:
                             | <get -> k>   -> state s (\-> k s)
                             | <put s -> k> -> state s (\-> k <Unit.0>)
                           | y -> y

                   -- TODO make List typecheck. IE Not ListF
                   map : forall X Y. {{X -> Y} -> <List X> -> <List Y>}
                       = \f lst -> case lst of
                         | <nil>       -> <ListF.0>
                         | <cons x xs> -> <ListF.1 (f x) (map f xs)>

                   fst : forall X Y. {X -> Y -> X}
                       = \x y -> x

                   next : forall. {[<State <Int>>] <Int>}
                        = \-> fst get! (put (add get! one))

                   index
                     : forall X. {<List X> -> <List <Pair <Int> X>>}
                     = \xs -> state zero (\-> map (\x -> <Pair.0 next! x>) xs)

                   actual : forall. {[<State <Int>>] <Int>}
                          = \-> index abc!

                   abc : forall. {<List <Char>>}
                       = \-> cons a (cons b (cons c nil))

                   expected : forall. {[<State <Int>>] <Int>}
                            = \-> cons <Pair.0 zero a>
                                    (cons <Pair.0 one b>
                                      (cons <Pair.0 two c> nil))

                 in checkEqual actual! expected!
               |]

               add = Command intOpsId 0
               get = Command stateCid 0
               put = Command stateCid 1

               (zero, zeroVal) = mkForeignTm @Int intId [] 0
               (one, oneVal) = mkForeignTm @Int intId [] 1
               (two, twoVal) = mkForeignTm @Int intId [] 2

               (a, aVal) = mkForeignTm @Text textId [] "a"
               (b, bVal) = mkForeignTm @Text textId [] "b"
               (c, cVal) = mkForeignTm @Text textId [] "c"

               -- pair a b  = DataConstructor pairId 0 [a, b]

               -- TODO:
               -- * these definitions are copied from HaskellForeign.Test
               -- * HaskellForeign.Test duplicates the ListF defn
               -- lfixTm x   = DataConstructor lfixId 0 [x]
               -- lcons x xs = lfixTm (DataConstructor listfId 1 [x, xs])
               -- lnil       = lfixTm (DataConstructor listfId 0 [])

               resolutionState = fromList $
                 -- Provides State, List, Pair
                 Frank.resolvedDecls ^. globalCids <>
                 testingDecls ^. globalCids <>
                 [("Int", intId)]

              Just (listId, _) <- pure $ namedData "ListF" Frank.resolvedDecls

              let store = storeOf $ toIpld <$>
                    [ zeroVal
                    , oneVal
                    , twoVal
                    , aVal
                    , bVal
                    , cVal
                    ]

              Right test' <- pure $ resolveTm resolutionState test
              let test'' = substituteAll
                    [ ("add", add)
                    , ("get", get)
                    , ("put", put)
                    , ("zero", zero)
                    , ("one", one)
                    , ("two", two)
                    , ("a", a)
                    , ("b", b)
                    , ("c", c)
                    , ("checkEqual", checkEqual)
                    , ("cons", Lambda ["x", "xs"] (DataConstructor listId 1 [V"x", V"xs"]))
                    , ("nil", DataConstructor listId 0 [])
                    ]
                    test'
              runTest "next one" testingHandlers store test'' (Right unit)
         ]

       -- Example from "Continuation Passing Style for Effect Handlers"
       -- - Hillerström, Lindley, Atkey, Sivaramakrishnan
       , do
       let tm = forceTm [text|
         letrec
           ifthenelse : forall A. {<Bool> -> {A} -> {A} -> A}
                      = \b l r -> case b of
             | <False> -> r!
             | <True>  -> l!

           cons : forall A. {A -> <List A> -> <List A>}
                = \a as -> <List.1 a as>

           concat
             : forall A. {<List A> -> <List A> -> <List A>}
             = \xs ys -> case xs of
               | <nil> -> ys
               | <cons x xs> -> cons x (concat xs ys)

           singletonList
             : forall a. {A -> <List A>}
             = \a -> <List.1 a <List.0>>

           drunkToss
             : forall. {[<Choose <Bool>>, <Abort>] Toss}
             -- decide whether the coin is caught
             = \-> ifthenelse Choose.0!
                     -- decide the face
                     (\-> ifthenelse Choose.0! (\-> <Toss.0>) (\-> <Toss.1>))
                     (\-> Abort.0!)

           -- use a list to model nondeterminism
           -- nondet : forall A. {{[<Choose <Bool>>, <Abort>] A} -> <List A>}
           --        = \a -> handle a! : A with
           --          Choose:
           --            | <choose -> k> -> concat (k Bool.0) (k Bool.1)
           --          Abort:
           --            | <aborting -> k> -> emptyList
           --          | x -> singletonList x

           -- TODO:
           --   * should p come first or last?
           --   * can we use variables other than e yet?
           --   * change declarations format:
           --     - data and effects aren't really different?
           --     - toplevel letrec is weird - instead make it implicit
           --   * nits
           --     - really would be nice to remove some angle brackets
           --     - s/Bool.0/True
           allChoices : forall A. {{[p, <Choose <Bool>>] A} -> [p] <List <A>>}
                      = \a -> handle a! : A with
                        Choose:
                          | <choose -> k> -> concat (k <Bool.0>) (k <Bool.1>)
                        | x -> singletonList x

           failure : forall A. {{[p, <Abort>] A} -> [p] <List <A>>}
                   = \a -> handle a! : A with
                     Abort:
                       | <aborting -> k> -> <List.0>
                     | x -> singletonList x

           -- should give []
           composition1
             : forall A. {{[<Choose <Bool>>, <Abort>] A} -> <List <List A>>}
             = \a -> failure (\-> allChoices a)

           -- should give [[Heads], [Tails], []]
           composition2
             : forall A. {{[<Choose <Bool>>, <Abort>] A} -> <List <List A>>}
             = \a -> allChoices (\-> failure a)

           actual1
             : forall. {<List <List <Toss>>>}
             = \-> composition1 drunkToss

           expected1
             : forall. {<List <List <Toss>>>}
             = \-> <List.0>

           actual2
             : forall. {<List <List <Toss>>>}
             = \-> composition2 drunkToss

           -- [[Heads], [Tails], []]
           -- = [Heads]:[Tails]:[]:Nil
           -- = (Heads:Nil):(Tails:Nil):Nil:Nil
           -- = (cons (cons Heads Nil) (cons (cons Tails Nil) (cons Nil Nil)))
           expected2
             : forall. {<List <List <Toss>>>}
             = \-> cons
               (cons Heads <List.0>)
               (cons
                 (cons Tails <List.0>)
                 (cons <List.0> <List.0>))

         in checkEqual actual1! expected1! -- TODO actual2! expected2!
         |]

         -- TODO check if these are used
       let resolutionState = fromList $
             -- Provides State, List, Pair
             Frank.resolvedDecls ^. globalCids <>
             testingDecls ^. globalCids <>
             [("Int", intId)]

       Right tm' <- pure $ resolveTm resolutionState tm
       let tm'' = substituteAll
             [ ("checkEqual", checkEqual)
             ]
             tm'

       let store = emptyStore -- storeOf $ toIpld <$> []

       runTest "drunk toss" testingHandlers store tm'' (Right unit)
       ]
