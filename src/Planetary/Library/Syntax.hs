{-# language GADTs #-}
{-# language OverloadedStrings #-}
{-# language PatternSynonyms #-}
{-# language QuasiQuotes #-}
{-# language ScopedTypeVariables #-}
module Planetary.Library.Syntax where

import Data.Text (Text)
import NeatInterpolation
import Network.IPLD

import Planetary.Core
import Planetary.Support.Ids
import Planetary.Support.NameResolution
import Planetary.Support.Parser

import qualified Data.ByteString.Char8 as B8
import qualified Data.Text as T

cidText :: Cid -> Text
cidText = T.pack . B8.unpack . compact

vectorIdStr, uidMapIdStr, lfixIdStr :: Text
vectorIdStr = cidText vectorId
uidMapIdStr = cidText uidMapId
lfixIdStr   = cidText lfixId

decls :: [DeclS]
decls = forceDeclarations [text|
data InitiateAbility =
  | <openAbility>
  | <closedAbility>

-- mutually recursive family of data types
data TyFamily =
  | <valTy>
  | <compTy>
  | <peg>
  | <tyArg>
  | <ability>

-- TODO: GADT like syntax?
-- | dataTy : uid -> <vector ty> -> Ty ValTy uid a ty

data TyF uid a Ty =
  -- ValTy
  | <dataTy uid <vector Ty>>
  | <suspendedTy Ty>
  | <variableTy a>

  -- CompTy
  | <compTy <vector Ty> Ty>

  -- Peg
  | <peg Ty Ty>

  -- TyArg
  | <tyArgVal Ty>
  | <tyArgAbility Ty>

  -- Ability
  | <ability InitiateAbility <uidMap uid Ty>>

data Adjustment uid a =
 <adjustment <uidMap uid <lfix <Ty uid a>>>>

data TmFamily =
  <value>
  | <continuation>
  | <tm>
  | <adjustmentHandlers>

data Tm uid tyvar tmvar tm =
  -- Value
  <command uid row>
  | <dataConstructor uid row <vector tm>>
  | <foreignValue uid <vector <Ty uid tyvar>> uid>
  | <lambda <vector text> tm>

  -- Continuation
  | <application <vector tm>
  | <case uid <vector <tuple <vector text> tm>>
  | <handle <adjustment uid tyvar> <Ty uid tyvar> <tm uid tyvar tmvar> tm>
  | <let <polytype uid tyvar> text tm>

  -- Tm
  | <variable tmvar>
  | <instantiatePolyvar tmvar <vector <tyArg uid tyvar>>
  | <annotation tm <Ty uid tyvar>
  | <value <tm>>
  | <cut <tm> <tm>>
  | <letrec <vector <tuple <polytype uid tyvar> <tm>>> tm>

  -- AdjustmentHandlers
  | <adjustmentHandlers <uidMap uid <vector tm>>>
|]

resolvedDecls :: ResolvedDecls
Right resolvedDecls = nameResolution decls $ uIdMapFromList
  [ ("vector", vectorId)
  , ("uidMap", uidMapId)
  , ("lfix", lfixId)
  , ("row", rowId)
  , ("text", textId)
  , ("tuple", tupleId)
  ]
tyId :: Cid
Just (tyId, _) = namedData "Ty" resolvedDecls

pattern VarTyVal :: Int -> TyArg uid
pattern VarTyVal a = TyArgVal (BoundVariableTy a)

-- TODO: typecheck using this table
syntaxInterfaceTable :: InterfaceTableI
syntaxInterfaceTable =
  let -- poor man's variables
      uid = 0
      a = 1

      fixTy = DataTy lfixId
        [ TyArgVal
           (DataTy tyId
             [ VarTyVal uid
             , VarTyVal a
             ]
           )
        ]
      tyTy = DataTy tyId
        [ VarTyVal uid
        , VarTyVal a
        , TyArgVal fixTy
        ]

  in uIdMapFromList
    [ (syntaxOpsId, EffectInterface [("uid", ValTyK), ("a", ValTyK)]
      -- Fix :: f (Fix f) -> Fix f
      -- FixTy :: Ty uid a (Fix (Ty uid a)) -> Fix (Ty uid a)
      -- XXX
      [ CommandDeclaration "fix" [tyTy] fixTy
      -- unFix :: Fix f  -> f (Fix f)
      -- unFixTy :: Fix (Ty uid a) -> Ty uid a (Fix (Ty uid a))
      , CommandDeclaration "unfix" [fixTy] tyTy
      ])
    ]
