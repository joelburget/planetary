{-# language DataKinds #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language Rank2Types #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Core.Eval.Test (unitTests, runTest, mkLogger) where

import Control.Lens
import Control.Monad.Reader (asks)
import Control.Monad.IO.Class
import Data.Maybe (fromJust)
import Data.Text (Text)
import NeatInterpolation
import Network.IPLD (Cid, toIpld)
import Prelude hiding (not)
import EasyTest hiding (bool, run)

import Planetary.Core hiding (logIncomplete, logReturnState, logValue)
import Planetary.Support.Ids hiding (boolId) -- XXX fix this
import Planetary.Support.Parser (forceTm)
import Planetary.Support.Pretty
import Planetary.Library
import qualified Planetary.Library.FrankExamples as Frank
import Planetary.Library.HaskellForeign (mkForeignTm, haskellOracles, intOpsId)

import Data.Text.Prettyprint.Doc

-- Some more good examples here:
-- https://github.com/dhil/links/blob/master/examples/handlers/shallow_state.links

noteFailureState
  :: EvalState -> Either Err TmI -> Either Err TmI -> Test ()
noteFailureState initState result expected = do
  note $ layout $ vsep
    [ ""
    , annotate Error "fail with initial state:"
    , prettyEvalState initState
    , ""
    , annotate Error "got:"
    , either pretty (prettyTmPrec 11) result
    , ""
    , annotate Error "expected:"
    , either pretty (prettyTmPrec 11) expected
    ]
  fail "failure: see above"

putLogs :: Bool
putLogs = False

mkLogger :: (Text -> IO ()) -> Logger
mkLogger mkNote =
  let helper :: forall a. (a -> Text) -> a -> IO ()
      helper f = if putLogs then mkNote . f else const (pure ())
  in Logger (helper . logReturnState) (helper logIncomplete) (helper logValue)

runTest
  :: Text
  -> AmbientHandlers
  -> ValueStore
  -> TmI
  -> Either Err TmI
  -> Test ()
runTest name handlers store tm expected = scope name $ do
  let initState = initEvalState store tm
  logger <- mkLogger <$> asks note_
  result <- liftIO $ run handlers logger initState
  if result == expected
     then ok
     else noteFailureState initState result expected

boolId :: Cid
(boolId, _) = fromJust $ namedData "Bool" Frank.resolvedDecls

bool :: Int -> TmI
bool i = DataConstructor boolId i []

unitTests :: Test ()
unitTests  =
  let
      -- true, false :: forall a b. Tm Cid a b
      false = bool 0
      true = bool 1

      not tm = Case tm
        [ ([], true)
        , ([], false)
        ]

      evalEnvRunTest desc = runTest desc noAmbientHandlers emptyStore

  in scope "evaluation" $ tests
       [ let x = V"x"
             -- tm = forceTm "(\y -> y) x"
             lam = Lambda ["x"] x
         in scope "functions" $ tests
            -- [ evalEnvRunTest "application 1" (AppN lam [true])
            --   (Right true)
            [ evalEnvRunTest "application"
              (AppT lam [true])
              (Right true)
            -- TODO: test further steps with bound variables
            , evalEnvRunTest "nullary function call"
              (AppT (Lambda [] true) [])
              (Right true)
            ]

       , scope "case" $ tests
         [ evalEnvRunTest "not (1)" (not false) (Right true)
         , evalEnvRunTest "not (2)" (not true)  (Right false)
         ]

       , let ty :: Polytype Cid
             ty = Polytype [] (DataTy (UidTy boolId) [])

             tm = Let false ty "x" (V"x")
         in scope "let" $ evalEnvRunTest "let x = false in x" tm (Right false)

       , scope "handle" $ do
       let abortHandlerTm = forceTm [text|
               handle x : [e , <Abort>]Int with
                 Abort:
                   | <aborting -> k> -> one
                 | v -> two
             |]

           sendHandlerTm = forceTm [text|
               handle x : [e, <Send Int>]Int with
                 Send:
                   | <send n -> k> -> n
                 | v -> v
             |]

           -- TODO: this is duplicated in FrankExamples.Test
           stateHandlerTm = forceTm [text|
               letrec
                 state : forall S X. {S -> {X} -> X}
                       = \s x -> handle x! : X with
                         State:
                           | <get -> k>   -> state s (\-> k s)
                           | <put s -> k> -> state s (\-> k <Unit.0>)
                         | y -> y

                 fst : forall X Y. {X -> Y -> X}
                     = \x y -> x

                 -- increment, return original value
                 next : forall. {[<State Int>]Int}
                      -- fst get! (put (get! + 1))
                      = \-> fst get! (put (add get! one))

                 statefulTm
                   : forall. {[<State Int>] Int}
                   = \-> let x : forall. Int = next! in
                           let y : forall. Int = next! in
                             let z : forall. Int = next! in z

               in state zero statefulTm
             |]

           (zero, zeroVal) = mkForeignTm @Int intId [] 0
           (one,  oneVal)  = mkForeignTm @Int intId [] 1
           (two,  twoVal)  = mkForeignTm @Int intId [] 2

       Right abortHandler <- pure $ resolve $ fst abortHandlerTm
       Right sendHandler  <- pure $ resolve $ fst sendHandlerTm
       Right stateHandler <- pure $ resolve $ fst stateHandlerTm

       Just abortCid <- pure $ Frank.resolvedDecls ^? globalCids . ix "Abort"
       Just sendCid  <- pure $ Frank.resolvedDecls ^? globalCids . ix "Send"
       Just stateCid <- pure $ Frank.resolvedDecls ^? globalCids . ix "State"

       let abortHandler' = substitute "one" one $
             substitute "two" two
               abortHandler

           handleVal = substitute "x" zero abortHandler'

           abort = AppN (Command abortCid 0) []
           handleAbort = substitute "x" abort abortHandler'

           handleSend = substitute "x"
             (AppN (Command sendCid 0) [one])
             sendHandler

           get = Command stateCid 0
           put = Command stateCid 1
           add = Command intOpsId 0

           handleNext = substituteAll
             [ ("zero", zero)
             , ("one", one)
             , ("get", get)
             , ("put", put)
             , ("add", add)
             ]
             stateHandler

           numberStore = storeOf $ toIpld <$> [zeroVal, oneVal, twoVal]

       tests
         [ runTest "val" noAmbientHandlers emptyStore handleVal
           (Right two)
         , runTest "abort" noAmbientHandlers emptyStore
           handleAbort (Right one)
         , runTest "send" noAmbientHandlers emptyStore handleSend
           (Right one)
         , let handlers = AmbientHandlers haskellOracles
           in runTest "handle state" handlers numberStore handleNext (Right two)
         ]

       , scope "let x = false in let y = not x in not y" $ do
         let
             ty = Polytype [] (DataTy (UidTy boolId) [])
             tm = Let false ty "x" $
                    Let (not (V"x")) ty "y" $
                      not (V"y")

             -- both versions of tm should be equivalent
         Right tm2 <- pure $ resolve $ fst $ forceTm [text|
             let not: forall. {<Bool> -> <Bool>}
                    = \x -> case x of
                      | <False> -> <Bool.1>
                      | <True>  -> <Bool.0>
             in
             let x: forall. Bool = false in
             let y: forall. Bool = not x in
             not y
           |]
         let tm2' = substitute "false" false tm2

         tests
           [ evalEnvRunTest "tm"  tm   (Right false)
           , evalEnvRunTest "tm2" tm2' (Right false)
           ]

       , scope "letrec" $ do
       let evenodd = fst $ forceTm [text|
             letrec
               even : forall. {<Fix NatF> -> <Bool>}
                    = \n -> case n of
                      | <z>       -> <Bool.1> -- true
                      | <succ n'> -> odd n'
               odd : forall. {<Fix NatF> -> <Bool>}
                   = \m -> case m of
                     | <z>       -> <Bool.0> -- false
                     | <succ m'> -> even m'
             in body
           |]
           -- mkFix = Command fixOpsId 0
           -- unFix = Command fixOpsId 1

       Right evenodd' <- pure $ resolve evenodd

       Just (natfId, _)  <- pure $ namedData "NatF" Frank.resolvedDecls

       let -- mkTm n = [| evenOdd n |]
           mkTm :: Text -> Int -> TmI
           mkTm fnName n =
             let mkNat 0 = DataConstructor natfId 0 []
                 mkNat k = DataConstructor natfId 1 [mkNat (k - 1)]

                 tm = substitute "body"
                   (AppT (V fnName) [mkNat n])
                   evenodd'
             in tm

           handlers = AmbientHandlers haskellOracles
           runTest' desc = runTest desc handlers emptyStore

       tests
         [ runTest' "even 0"    (mkTm "even" 0)    (Right true)
         , runTest' "odd 0"     (mkTm "odd"  0)    (Right false)
         , runTest' "even 1"    (mkTm "even" 1)    (Right false)
         , runTest' "odd 1"     (mkTm "odd"  1)    (Right true)
         , runTest' "even 7"    (mkTm "even" 7)    (Right false)
         , runTest' "odd 7"     (mkTm "odd"  7)    (Right true)
         , runTest' "even 10"   (mkTm "even" 10)   (Right true)
         , runTest' "odd 10"    (mkTm "odd"  10)   (Right false)
         , runTest' "odd 20"    (mkTm "odd"  20)   (Right false)
         , runTest' "even 100"  (mkTm "even" 100)  (Right true)
         ]

       , scope "closures" $ do
       let tm = fst $ forceTm [text|
             letrec
               const
                 : forall. {<Text> -> {<Text> -> <Text>}}
                 = \x -> \y -> x

               -- capture x, then shadow
               actual1
                 : forall. {<Text>}
                 = \->
                   let foo' : forall. {<Text> -> <Text>} = const foo in
                   let x : forall. <Text> = bar in
                   foo' bar

               expected1
                 : forall. {<Text>}
                 = \-> foo
             in actual1!
           |]

       let tm2 = fst $ forceTm [text|
             letrec
               captureX
                 : forall. {<Text> -> <Pair {<Text> -> <Text>} <Text>>}
                 = \x -> <Pair.0 (\y -> x) x>

               -- capture x, then shadow
               actual1
                 : forall. {<Text>}
                 = \->
                   let pair : forall. <Pair {<Text> -> <Text>} <Text>> = captureX foo in
                   case pair of
                     | <pair f x> -> f bar

               expected1
                 : forall. {<Text>}
                 = \-> foo
             in actual1!
           |]

       Right tm'  <- pure $ resolve tm
       Right tm2' <- pure $ resolve tm2

       let (foo, fooVal) = mkForeignTm @Text intId [] "foo"
           (bar, barVal) = mkForeignTm @Text intId [] "bar"
           (baz, bazVal) = mkForeignTm @Text intId [] "baz"
           subs =
             [ ("foo", foo)
             , ("bar", bar)
             , ("baz", baz)
             ]

       let tm''  = substituteAll subs tm'
           tm2'' = substituteAll subs tm2'

           store = storeOf $ toIpld <$> [fooVal, barVal, bazVal]

       tests
         [ runTest "const" noAmbientHandlers store tm'' (Right foo)
         , runTest "pair"  noAmbientHandlers store tm2'' (Right foo)
         ]
       ]
