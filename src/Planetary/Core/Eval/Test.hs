{-# language DataKinds #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Core.Eval.Test (unitTests, stepTest, runTest, mkLogger) where

import Control.Arrow (right)
import Control.Lens
import Control.Monad (when)
import Control.Monad.Reader (asks)
import Control.Monad.IO.Class
import qualified Data.HashMap.Strict as HashMap
import Data.Text (Text)
import NeatInterpolation
import Network.IPLD as IPLD
import Prelude hiding (not)
import EasyTest hiding (bool, run)

import Planetary.Core hiding (logIncomplete, logReturnState)
import Planetary.Support.Ids hiding (boolId) -- XXX fix this
import Planetary.Support.NameResolution (resolveTm, closeTm)
import Planetary.Support.Parser (forceTm)
import Planetary.Support.Pretty
import qualified Planetary.Library.FrankExamples as Frank
import Planetary.Library.HaskellForeign (mkForeignTm, haskellOracles)
import qualified Planetary.Library.HaskellForeign as HaskellForeign

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal

noteFailureState
  :: EvalState -> Either Err EvalState -> Either Err TmI -> Test ()
noteFailureState initState result expected = do
  note $ layout $ vsep
    [ ""
    , annotate Error "fail with initial state:"
    , prettyEvalState initState
    , ""
    , annotate Error "got:"
    , either pretty prettyEvalState result
    , ""
    , annotate Error "expected:"
    , either pretty (prettyTmPrec 11) expected
    ]
  fail "failure: see above"

putLogs :: Bool
putLogs = True

mkLogger :: (Text -> IO ()) -> Logger
mkLogger note_ = Logger
  (\t st -> note_ (logReturnState t st))
  (note_ . logIncomplete)

stepTest
  :: Text
  -> AmbientHandlers
  -> ValueStore
  -> Int
  -> TmI
  -> Either Err TmI
  -> Test ()
stepTest name handlers store steps tm expected =
  let applications :: [EvalM EvalState]
      applications = iterate (step =<<) (pure initState)
      initState = initEvalState store tm
      actual = applications !! steps

  in scope name $ do
    when putLogs $ note $ layout $ vsep
      [ "stepTest on:"
      , prettyEvalState initState
      ]

    logger <- mkLogger <$> asks note_
    result <- liftIO $ runEvalM handlers logger actual

    let result' = right _evalFocus result

    if result' == expected
    then ok
    else noteFailureState initState result expected

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
  if right _evalFocus result == expected
     then ok
     else noteFailureState initState result expected

boolId :: Cid
Just (boolId, _) = namedData "Bool" Frank.resolvedDecls

bool :: Int -> Tm Cid
bool i = DataConstructor boolId i []

unitTests :: Test ()
unitTests  =
  let
      noHandlers :: AmbientHandlers
      noHandlers = mempty

      -- true, false :: forall a b. Tm Cid a b
      false = bool 0
      true = bool 1

      not tm = CaseP tm
        [ ([], true)
        , ([], false)
        ]
      -- boolOfInt = Case boolId
      --   [ ([], one)
      --   , ([], zero)
      --   ]

      evalEnvRunTest desc = runTest desc noAmbientHandlers emptyStore

  in scope "evaluation" $ tests
       [ let x = BV 0 0
             -- tm = forceTm "(\y -> y) x"
             lam = Lam ["X"] x
         in scope "functions" $ tests
            [ evalEnvRunTest "application 1" (AppN lam [x]) (Right x)
            , evalEnvRunTest "application 2"
              (AppT lam [x])
              (Right x)
            -- TODO: test further steps with bound variables
            ]

       , scope "case" $ tests
         [ evalEnvRunTest "case False of { False -> True; True -> False }"
             (not false)
             (Right true)
         , evalEnvRunTest "case True of { False -> True; True -> False }"
             (not true)
             (Right false)

         , evalEnvRunTest "not false"
           (not false)
           (Right true)
         ]

       , let ty :: Polytype Cid
             ty = Polytype [] (DataTy (UidTy boolId) [])
             -- TODO: remove shadowing
             tm = close1 "x" $ let_ "x" ty false (FV"x")
         in scope "let" $ tests
            [ evalEnvRunTest "let x = false in x" tm
              (Right false)
            , evalEnvRunTest "let x = false in x" tm
              (Right false)
            ]

       , let handler = forceTm [text|
               handle x : [e , <Abort>]Int with
                 Abort:
                   | <aborting -> k> -> one
                 | v -> two
             |]

             zero = mkForeignTm @Int intId [] 0
             one  = mkForeignTm @Int intId [] 1
             two  = mkForeignTm @Int intId [] 2

             resolutionState = fromList $
               -- Provides Abort
               (Frank.resolvedDecls ^. globalCids) ++
               [("Int", intId)]

             Right handler' = resolveTm resolutionState handler
             handler'' = substitute "one" one $
               substitute "two" two
                 handler'

             handleVal = substitute "x" zero handler''

             abortCid = Frank.resolvedDecls ^?!
               globalCids . to HashMap.fromList . ix "Abort"
             abort = AppN (Command abortCid 0) []
             handleAbort = substitute "x" abort handler''
         in scope "handle" $ tests
              -- [ runTest "handle val" handleVal (Right two)
              [ runTest "handle abort" noAmbientHandlers emptyStore
                handleAbort (Right one)
              -- XXX test continuing from handler
              ]

--        , let
--              ty = Polytype [] (DataTy (UidTy boolId) [])
--              tm = close1 "x" $
--                   let_ "x" ty false $
--                     let_ "y" ty (not (FV"x")) $
--                       not (FV"y")

--              -- both versions of tm should be equivalent
--              resolutionState = todo "resolutionState"
--              Right tm2 = resolveTm resolutionState $ forceTm [text|
--                let x: forall. Bool = false in
--                  let y: forall. Bool = not x in
--                    not y
--              |]

--          in scope "let x = false in let y = not x in not y" $ tests
--               [ evalEnvRunTest "tm"  tm  (Right false)
--               -- , evalEnvRunTest "tm2" tm2 (Right false)
--               ]

       , let evenodd = forceTm [text|
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

             Right evenodd' = resolveTm
               -- Provides NatF, Bool
               (fromList (Frank.resolvedDecls ^. globalCids) <>
                [("Fix", lfixId)])
               evenodd

             -- mkFix = Command fixOpsId 0
             -- unFix = Command fixOpsId 1
             Just (natfId, _) = namedData "NatF" Frank.resolvedDecls
             Just (_, fixDecl) = namedInterface "FixOps" HaskellForeign.resolvedDecls
             EffectInterface fixBinders fixCtrs = fixDecl

             [_, CommandDeclaration _ _ unfixResult] = fixCtrs
             unfixTy = Polytype fixBinders unfixResult

             -- mkTm n = [| evenOdd n |]
             mkTm :: Text -> Int -> Tm Cid
             mkTm fnName n =
               let mkNat 0 = DataConstructor natfId 0 []
                   mkNat k = DataConstructor natfId 1 [mkNat (k - 1)]

                   Right tm = closeTm $
                     -- substitute "unFix" unFix $
                       substitute "body"
                         (AppT (FV fnName) [mkNat n])
                         evenodd'
               in tm

             handlers = AmbientHandlers haskellOracles
             stepTest' desc = stepTest desc handlers emptyStore

         in scope "letrec" $ tests
              [ stepTest' "even 0"  12  (mkTm "even" 0)  (Right true)
              , stepTest' "odd 0"   12  (mkTm "odd"  0)  (Right false)
              , stepTest' "even 1"  25 (mkTm "even" 1)  (Right false)
              -- , stepTest' "even 2"  16 (mkTm "even" 2)  (Right true)
              -- , stepTest' "even 7"  8  (mkTm "even" 7)  (Right false)
              -- , stepTest' "even 10" 11 (mkTm "even" 10) (Right true)
              -- , stepTest' "odd 7"   8  (mkTm "odd"  7)  (Right true)
              -- , stepTest' "odd 10"  11 (mkTm "odd"  10) (Right false)
              ]
       ]
