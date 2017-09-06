{-# language DataKinds #-}
{-# language OverloadedLists #-}
{-# language OverloadedStrings #-}
{-# language QuasiQuotes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}
module Planetary.Core.Eval.Test (unitTests, runTest, mkLogger) where

import Control.Lens
import Control.Monad.Reader (asks)
import Control.Monad.IO.Class
import qualified Data.HashMap.Strict as HashMap
import Data.Maybe (fromJust)
import Data.Text (Text)
import NeatInterpolation
import Network.IPLD (Cid)
import Prelude hiding (not)
import EasyTest hiding (bool, run)

import Planetary.Core hiding (logIncomplete, logReturnState, logValue)
import Planetary.Support.Ids hiding (boolId) -- XXX fix this
import Planetary.Support.NameResolution (resolveTm, closeTm)
import Planetary.Support.Parser (forceTm)
import Planetary.Support.Pretty
import qualified Planetary.Library.FrankExamples as Frank
import Planetary.Library.HaskellForeign (mkForeignTm, haskellOracles)

import Data.Text.Prettyprint.Doc

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
putLogs = True

mkLogger :: (Text -> IO ()) -> Logger
mkLogger mkNote = Logger
  (\t -> if putLogs then mkNote  . logReturnState t else const (pure ()))
  (if putLogs then mkNote . logIncomplete else const (pure ()))
  (if putLogs then mkNote . logValue      else const (pure ()))

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
      -- noHandlers :: AmbientHandlers
      -- noHandlers = mempty

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
            -- [ evalEnvRunTest "application 1" (AppN lam [true])
            --   (Right true)
            [ evalEnvRunTest "application 2"
              (AppT lam [true])
              (Right true)
            -- TODO: test further steps with bound variables
            ]

       , scope "case" $ tests
         [ evalEnvRunTest "case False of { False -> True; True -> False } (1)"
             (not false)
             (Right true)
         , evalEnvRunTest "case True of { False -> True; True -> False } (1)"
             (not true)
             (Right false)

         -- commenting these out because I don't think they're well formed
         -- terms
         -- , evalEnvRunTest "case False of { False -> True; True -> False } (2)"
         --     (not false)
         --     (Right true)
         -- , evalEnvRunTest "case True of { False -> True; True -> False } (2)"
         --     (not true)
         --     (Right false)
         ]

       , let ty :: Polytype Cid
             ty = Polytype [] (DataTy (UidTy boolId) [])

             tm = close1 "x" $ let_ "x" ty false (FV"x")
         in scope "let" $ evalEnvRunTest "let x = false in x" tm (Right false)

       , scope "handle" $ do
       let handlerTm = forceTm [text|
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

       Right handler' <- pure $ resolveTm resolutionState handlerTm

       let handler'' = substitute "one" one $
             substitute "two" two
               handler'

           handleVal = substitute "x" zero handler''

           abortCid = Frank.resolvedDecls ^?!
             globalCids . to HashMap.fromList . ix "Abort"
           abort = AppN (Command abortCid 0) []
           handleAbort = substitute "x" abort handler''
       tests
         [ runTest "handle val" noAmbientHandlers emptyStore handleVal
           (Right two)
         , runTest "handle abort" noAmbientHandlers emptyStore
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

       , scope "letrec" $ do
       let evenodd = forceTm [text|
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

       Right evenodd' <- pure $ resolveTm
         -- Provides NatF, Bool
         (fromList (Frank.resolvedDecls ^. globalCids) <>
          [("Fix", lfixId)])
         evenodd

       Just (natfId, _)  <- pure $ namedData      "NatF"   Frank.resolvedDecls

       let -- mkTm n = [| evenOdd n |]
           mkTm :: Text -> Int -> TmI
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
       ]
