{-# language LambdaCase #-}
{-# language OverloadedStrings #-}
module Planetary.Support.Pretty where

import Control.Lens
import qualified Data.Map.Strict as Map
import Data.List (intersperse)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import Network.IPLD hiding (Row, Value, (.=))
import Data.Text.Encoding (decodeUtf8)
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal

import Planetary.Core
import Planetary.Util

data Ann = Highlighted | Error | Plain | Val | Term

annToAnsi :: Ann -> AnsiStyle
annToAnsi = \case
  Highlighted -> colorDull Blue
  Error       -> color Red <> bold
  Plain       -> mempty
  Val         -> colorDull Green
  Term        -> color Magenta

prettyPureContFrame :: PureContinuationFrame -> Doc Ann
prettyPureContFrame (PureFrame tm _env) = "*" <+> prettyTmPrec 0 tm

prettyPureCont :: Doc Ann -> Stack PureContinuationFrame -> Doc Ann
prettyPureCont name stk = vsep
  [ annotate Highlighted name
  , indent 2 $ vsep $ prettyPureContFrame <$> stk
  ]

lineVsep :: Text -> [Doc ann] -> Doc ann
lineVsep head =
  let lineFormatter i line = vsep
        [ pretty head <+> pretty i <> ": "
        , indent 2 line
        ]
  in vsep . intersperse "" . imap lineFormatter

prettyContHandler :: ContHandler -> Doc Ann
prettyContHandler EmptyHandler = "EmptyHandler"
prettyContHandler (Handler handlers (vName, vRhs) env) =
  let
      prettyHandler (uid, uidHandler) = pretty uid
        -- , indent 2 (align $ vsep $ fmap prettyRow uidHandler)
      handlers' = prettyHandler <$> toList handlers
  in "handle" <+> list handlers'

prettyCont :: Continuation -> Doc Ann
prettyCont (Continuation stk) =
  let prettyContFrame (ContinuationFrame pureCont h@(Handler _handlers _valHandler _env)) = vsep
        [ "handler: " <> prettyContHandler h
        , prettyPureCont "pure cont:" pureCont
        ]
      prettyContFrame (ContinuationFrame pureCont EmptyHandler) = vsep
        [ "empty handler"
        , prettyPureCont "pure cont:" pureCont
        ]
      lines = prettyContFrame <$> stk
  in lineVsep "line" lines

prettyBinding :: Text -> BindingType -> Doc Ann
prettyBinding name = \case
  RecursiveBinding _env tms -> prettyTmPrec 0 (tms ^?! ix name)
  NonrecursiveBinding tm    -> prettyTmPrec 0 tm
  ContBinding cont          -> prettyCont cont

prettyEnv :: ValueStore -> Env -> Doc Ann
prettyEnv store env =
  let prettyCidLookup :: Text -> Cid -> Doc Ann
      prettyCidLookup name cid = fromMaybe (parens $ "cid failed lookup: " <> pretty cid) $ do
        ipld    <- store ^? ix cid
        binding <- fromIpld ipld :: Maybe BindingType
        pure $ prettyBinding name binding
      prettyLine :: Text -> Cid -> Doc Ann
      prettyLine name cid = sep
        [ pretty name <> ":"
        , indent 2 $ prettyCidLookup name cid
        ]
  in vsep $ fmap snd $ Map.toList $ imap prettyLine env

prettyEvalState :: EvalState -> Doc Ann
prettyEvalState (EvalState focus env store cont fwdCont) = vsep
  [ "EvalState"
  , indent 2 $ vsep
    [ annotate Highlighted "focus:" <+> prettyTmPrec 0 focus
    , annotate Highlighted "env:"
    , indent 2 (prettyEnv store env)
    , "cont:"
    , indent 2 (prettyCont cont)
    , case fwdCont of
        Nothing       -> mempty
        Just fwdCont' -> vsep
          [ "fwd cont:"
          , indent 2 (prettyCont fwdCont')
          ]
    ]
  ]

-- prettySequence :: [Doc ann] -> Doc ann
-- prettySequence xs =
--   let open      = flatAlt "" "{ "
--       close     = flatAlt "" " }"
--       separator = flatAlt "" "; "
--   in group (encloseSep open close separator xs)

prettyTyPrec :: (IsUid uid, Pretty uid) => Int -> TyFix uid -> Doc ann
prettyTyPrec d = \case
  DataTy ty tys -> angles $ fillSep $ prettyTyPrec 0 <$> ty : tys
  SuspendedTy ty -> braces $ prettyTyPrec 0 ty
  VariableTy t -> pretty t
  UidTy uid -> pretty uid
  CompTy args peg -> fillSep $ intersperse "->" $
    prettyTyPrec 0 <$> args ++ [peg]
  Peg ab ty -> showParens d $ prettyTyPrec d ab <+> prettyTyPrec d ty
  TyArgVal ty -> prettyTyPrec d ty
  TyArgAbility ab -> prettyTyPrec d ab
  Ability init mapping ->
    let initP = case init of
          -- TODO real name
          OpenAbility -> "e"
          ClosedAbility -> "0"
        -- prettyArgs :: [TyFix uid] -> Doc ann
        prettyArgs = fillSep . fmap (prettyTyPrec 0)
        flatArgs = (\(i, r) -> pretty i <+> prettyArgs r) <$> toList mapping
        flatArgs' = if null flatArgs then [] else "+" : flatArgs

    in brackets $ fillSep $ initP : flatArgs'

prettyPolytype :: (IsUid uid, Pretty uid) => Int -> Polytype uid -> Doc ann
prettyPolytype d (Polytype binders val) =
  let prettyBinder (name, kind) = case kind of
        ValTyK -> pretty name
        EffTyK -> brackets (pretty name)
      prettyBinders = case binders of
        [] -> ""
        _ -> " " <> fillSep (prettyBinder <$> binders)
  in "forall" <> prettyBinders <> "." <+> prettyTyPrec d val

showParens :: Int -> Doc ann -> Doc ann
showParens i = if i > 10 then parens else id

prettyTmPrec :: (IsUid uid, Pretty uid) => Int -> Tm uid -> Doc Ann
prettyTmPrec d = \case
  Variable t -> pretty t
  DataConstructor uid row args -> angles $ fillSep $
    let d' = if length args > 1 then 11 else 0
    in (pretty uid <> "." <> pretty row) : (prettyTmPrec d' <$> args)
  ForeignValue ty args locator -> showParens d $ fillSep $
    let d' = if length args > 1 then 11 else 0
    in "Foreign @" <> pretty ty : (prettyTyPrec d' <$> args) ++ [pretty locator]
  Lambda names body -> showParens d $
    "\\" <> fillSep (pretty <$> names) <+> "->" <+> prettyTmPrec 0 body
  Command uid row -> pretty uid <> "." <> pretty row
  Annotation tm ty -> parens $ fillSep [prettyTmPrec 0 tm, ":", prettyTyPrec 0 ty]
  -- TODO: show the division between normalized / non-normalized
  Application tm spine -> case spine of
    MixedSpine [] [] -> prettyTmPrec d tm <> "!"
    MixedSpine vals tms -> showParens d $ fillSep $
      prettyTmPrec 11 tm :
      fmap (annotate Val . prettyTmPrec 11) vals <>
      fmap (annotate Term  . prettyTmPrec 11) tms
    -- _ -> fillSep $ prettyTmPrec d <$> (tm : Foldable.toList spine)

  Case scrutinee handlers -> vsep
    [ "case" <+> prettyTmPrec 0 scrutinee <+> "of"
    -- TODO: use align or hang?
    , indent 2 $ vsep $ flip fmap handlers $ \(names, body) -> fillSep
      [ "|"
      , angles $ fillSep $ "_" : fmap pretty names
      , "->"
      , prettyTmPrec 0 body
      ]
    ]

  Handle tm _adj peg handlers (vName, vRhs) ->
    let
        prettyRow (names, kName, rhs) = fillSep
          ["|"
          , angles $ fillSep ("_" : fmap pretty names ++ ["->", pretty kName])
          , "->"
          , prettyTmPrec 0 rhs
          ]
        prettyHandler (uid, uidHandler) = vsep
          [ pretty uid <> colon
          , indent 2 (align $ vsep $ fmap prettyRow uidHandler)
          ]
        handlers' = prettyHandler <$> toList handlers
    in vsep
         [ "handle" <+> prettyTmPrec 0 tm <+> colon <+> prettyTyPrec 0 peg <+> "with"
         , indent 2 (align $ vsep handlers')
         , indent 2 $ fillSep
           [ "|"
           , pretty vName
           , "->"
           , prettyTmPrec 0 vRhs
           ]
         ]

  Let body ty name rhs -> fillSep
    [ "let"
    , pretty name
    , ":"
    , prettyPolytype 0 ty
    , "="
    , prettyTmPrec 0 body
    , "in"
    , prettyTmPrec 0 rhs
    ]

  Letrec names lambdas body ->
    let rowInfo = zip names lambdas
        rows = flip fmap rowInfo $ \(name, (ty, lam)) -> vsep
          [ pretty name <+> colon <+> prettyPolytype 0 ty
          , indent 2 $ "=" <+> prettyTmPrec 0 lam
          ]
    in vsep
         [ "letrec"
         , indent 2 $ vsep rows
         , "in" <+> prettyTmPrec 0 body
         ]

  Closure names env tm ->
    let lamNames = pretty <$> names
        capturedNames = pretty <$> Map.keys env
    in showParens d $ sep
         [ "Closure"
         , list capturedNames
         , "\\" <> sep lamNames <+> "->"
         , prettyTmPrec 11 tm
         ]
  Hole -> "_Hole_"
  Value v -> annotate Val (prettyTmPrec d v)

instance Pretty Cid where
  pretty = pretty . Text.cons '…' . Text.takeEnd 5 . decodeUtf8 . compact

layout :: Doc Ann -> Text
layout = renderStrict .
  layoutSmart LayoutOptions {layoutPageWidth = AvailablePerLine 80 1} .
  reAnnotate annToAnsi

logReturnState :: Text -> EvalState -> Text
logReturnState name st = layout $ vsep
  [ "Result of applying:" <+> annotate Highlighted (pretty name)
  , prettyEvalState st
  , ""
  ]

logIncomplete :: EvalState -> Text
logIncomplete st = layout $ vsep
  [ annotate Error "incomplete: no rule to handle"
  , prettyEvalState st
  ]

logValue :: TmI -> Text
logValue val = layout $ vsep
  [ annotate Highlighted "logged value"
  , prettyTmPrec 0 val
  ]
