{-# language TypeFamilies #-}
module Planetary.Library (repo, resolve) where

import Control.Lens
import Data.Foldable (fold)

import Planetary.Core
import Planetary.Support.NameResolution
import Planetary.Support.Parser

import qualified Planetary.Library.FrankExamples  as Frank
import qualified Planetary.Library.HaskellForeign as HaskellForeign
import qualified Planetary.Library.Management     as Management
import qualified Planetary.Library.Meta           as Meta
import qualified Planetary.Library.StrNat         as StrNat
import qualified Planetary.Library.Syntax         as Syntax

repo :: ResolvedDecls
repo = fold
  [ Frank.resolvedDecls
  , HaskellForeign.resolvedDecls
  , Management.resolvedDecls
  , Meta.resolvedDecls
  , StrNat.resolvedDecls
  , Syntax.resolvedDecls
  ]

-- TODO: converting between uidmap and hashmap is weird
resolve :: Tm' -> Either ResolutionErr TmI
resolve = resolveTm (repo ^. globalCids . to toList . to fromList)
