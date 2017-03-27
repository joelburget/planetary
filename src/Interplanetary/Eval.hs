{-# language DataKinds #-}
{-# language GADTs #-}
{-# language LambdaCase #-}

module Interplanetary.Eval where

import Bound
import Control.Lens hiding ((??))
import Control.Lens.At (at)
import Control.Lens.Getter (view)
import Control.Monad.Reader
import Control.Monad.Trans.Either (EitherT(runEitherT), left)
import Data.Dynamic
import Data.HashMap.Lazy (HashMap)
import Data.Word (Word32)

import Interplanetary.Syntax
import Interplanetary.Util

type TmI = Tm Int Int

data Halt :: * where
  Stuck :: TmI -> Halt
  -- BadDynamic :: MultiHash -> Halt
  -- MissingOracle :: MultiHash -> Halt
  -- BadVecLookup :: Word32 -> Halt
  RowBound :: Halt

deriving instance Show Halt

type EvalContext = EitherT Halt (Reader ())

runContext :: () -> EvalContext TmI -> Either Halt TmI
runContext store ctxTm = runReader (runEitherT ctxTm) store

step :: TmI -> EvalContext TmI
step = \case
  -- TODO first case
  Case (Construct uid row applicands) rows -> do
    body <- (rows ^? ix row) ?? RowBound
    pure $ instantiate (applicands !!) body
  -- TODO handle cases
  Let (Polytype _pBinders pVal) rhs body ->
    let fTy' = instantiate (todo "instantiate with what?") pVal
        body' = instantiate1 (Annotation rhs fTy') body
    in pure body'

-- TODO find appropriate fixity
(??) :: Maybe a -> Halt -> EvalContext a
(Just a) ?? _ = pure a
Nothing ?? err = left err
