{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Library.FrankExamples.Test (unitTests) where

import Control.Exception (Exception, throw)
import Control.Lens
import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Text.IO as T
import Data.Text.Prettyprint.Doc
import Data.Typeable (Typeable)
import NeatInterpolation
import EasyTest hiding (run)

import Planetary.Core
import qualified Planetary.Library.FrankExamples as Frank
import Planetary.Core.Eval.Test (runTest, mkLogger)
import Planetary.Library.HaskellForeign (mkForeignTm, intOpsId)
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser
import Planetary.Support.Pretty

data NotGood = NotGood TmI TmI
  deriving Typeable

instance Exception NotGood

instance Show NotGood where
  show (NotGood a b)
    = "(" ++ show (prettyTmPrec 11 a) ++ "), " ++
      "(" ++ show (prettyTmPrec 11 b) ++ ")"

unitTests :: Test ()
unitTests =
  let testingDecls :: ResolvedDecls
      Right testingDecls = resolveDecls
        [ ("Unit", unitId)
        ] $ forceDeclarations [text|
          interface TestingOps A B =
            | checkEqual : A -> B -> <Unit>
        |]

      Just (checkingOpsId, _) = namedInterface "TestingOps" testingDecls

      unit = DataConstructor unitId 0 []

      -- This should check that the two terms are equal. If so it just exits
      -- with unit, otherwise it throws (to easytest).
      checkEqualImpl :: Handler
      checkEqualImpl st
        | AppN _ [tm1, tm2] <- st ^. evalFocus = do
          -- XXX testingEnv hack. this is really offensive
          let logger = mkLogger T.putStrLn
          (Right v1, _) <- liftIO $ run testingEnv logger (st & evalFocus .~ tm1)
          (Right v2, _) <- liftIO $ run testingEnv logger (st & evalFocus .~ tm2)
          if v1 == v2
             then pure $ st & evalFocus .~ unit
             else throw $ NotGood v1 v2
      checkEqualImpl _ = throwError FailedForeignFun

      testingEnv :: AmbientEnv
      testingEnv = AmbientEnv
        [ (checkingOpsId, [ checkEqualImpl ]) ]
        []

      checkEqual = Command checkingOpsId 0
  in scope "frank examples" $ tests
       [ scope "catch" $ tests []
       , scope "pipe" $ tests []
       , scope "spacer" $ tests []
       , scope "state" $ tests []
       , scope "next" $ tests
         [ let
               emptyEnv :: AmbientEnv
               emptyEnv = AmbientEnv mempty mempty

               test = forceTm [text|
                 letrec
                   -- note: not `forall S X. {S -> <State S>X -> X}`
                   state : forall S X. {S -> X -> X}
                         = \s x -> handle x : X with
                           State:
                             | <get -> k>   -> state s (k s)
                             | <put s -> k> -> state s (k <Unit.0>)
                           | x -> x

                   -- XXX make List typecheck
                   map : forall X Y. {{X -> Y} -> <List X> -> <List Y>}
                       = \f lst -> case lst of
                         ListF:
                           | <nil>       -> <ListF.0>
                           | <cons x xs> -> <ListF.1 (f x) (map f xs)>

                   next : forall. {[<State <Int>>] <Int>}
                        = \-> fst get! (put (add get! zero))

                   index : forall. {<List X> -> <List <Pair <Int> X>>}
                         = \xs -> state zero (map (\x -> <Pair.0 next! x>) xs)
                         --                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

                   actual : forall. {[<State <Int>>] <Int>}
                          = \-> index abc

                   expected : forall. {[<State <Int>>] <Int>}
                            = \-> cons <Pair.0 zero a>
                                    (cons <Pair.0 one b>
                                      (cons <Pair.0 two c> nil))

                 in checkEqual actual! expected!
               |]

               add = Command intOpsId 0
               abc = mkForeignTm @Text textId [] "abc"

               zero = mkForeignTm @Int intId [] 0
               one = mkForeignTm @Int intId [] 1
               two = mkForeignTm @Int intId [] 2

               a = mkForeignTm @Text textId [] "a"
               b = mkForeignTm @Text textId [] "b"
               c = mkForeignTm @Text textId [] "c"

               Just (listfId, _) = namedData "ListF" Frank.resolvedDecls
               Just (pairId,  _) = namedData "Pair"  Frank.resolvedDecls

               pair a b  = DataConstructor pairId 0 [a, b]

               -- TODO:
               -- * these definitions are copied from HaskellForeign.Test
               -- * HaskellForeign.Test duplicates the ListF defn
               lfixTm x   = DataConstructor lfixId 0 [x]
               lcons x xs = lfixTm (DataConstructor listfId 1 [x, xs])
               lnil       = lfixTm (DataConstructor listfId 0 [])

               resolutionState = fromList $
                 -- Provides State, List, Pair
                 Frank.resolvedDecls ^. globalCids <>
                 testingDecls ^. globalCids <>
                 [("Int", intId)]

               Right test' = resolveTm resolutionState test
               Right test'' = closeTm $
                 substituteAll
                   [ ("add", add)
                   , ("abc", abc)
                   , ("zero", zero)
                   , ("one", one)
                   , ("two", two)
                   , ("a", a)
                   , ("b", b)
                   , ("c", c)
                   , ("checkEqual", checkEqual)
                   ]
                   test'
            in do
                  io $ print $ vsep
                    [ ""
                    , prettyTmPrec 11 test
                    ]
                  runTest "next one" testingEnv test'' (Right unit)
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
           in do
             skip
             runTest "drunk toss TODO" undefined undefined undefined
       ]
