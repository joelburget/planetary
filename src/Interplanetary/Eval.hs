{-# language DataKinds #-}
{-# language GADTs #-}

module Interplanetary.Eval where

import Control.Lens.Getter (view)
import Control.Lens.At (at)
import Control.Monad.Reader
import Control.Monad.Trans.Either (EitherT(runEitherT), left)
import Data.Dynamic
import Data.HashMap.Lazy (HashMap)
import Data.Word (Word32)

import Interplanetary.Genesis

data Halt :: * where
  Stuck :: GenesisTerm -> Halt
  BadDynamic :: MultiHash -> Halt
  MissingOracle :: MultiHash -> Halt
  BadVecLookup :: Word32 -> Halt

deriving instance Show Halt

type Context = EitherT Halt (Reader OracleStore)

readOracle :: Typeable a => MultiHash -> Context a
readOracle addr = do
  mapContents <- view (at addr)
  case mapContents of
    Nothing -> left (MissingOracle addr)
    Just dyn ->
      case fromDynamic dyn of
        Nothing -> left (BadDynamic addr)
        Just a -> pure a

runContext :: OracleStore -> Context GenesisTerm -> Either Halt GenesisTerm
runContext store ctxTm = runReader (runEitherT ctxTm) store

step :: GenesisTerm -> Context GenesisTerm
step v@(Value _) = pure v
step c@(Covalue _) = pure c

step (Computation (Sum ix body) (Case branches))
  = domainLookup' (PositionalDomain branches) (Index ix)

-- Substitute all terms from the domain (destructured) in the body
step (Computation (Product subs) (Match body))
  = pure $ close body (PositionalDomain subs)

step e@(Oracle _) = left (Stuck e)
step var@(Bound _level _pos) = left (Stuck var) -- we're stuck
