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

type OracleStore = HashMap MultiHash Dynamic

data Halt :: * where
  Stuck :: GenesisTerm -> Halt
  BadDynamic :: MultiHash -> Halt
  MissingOracle :: MultiHash -> Halt
  BadDomainLookup :: Domain -> Location -> Halt
  BadVecLookup :: Word32 -> Halt

deriving instance Show Halt

type Context = EitherT Halt (Reader OracleStore)

domainLookup' :: Domain -> Location -> Context GenesisTerm
domainLookup' dom loc = case domainLookup dom loc of
  Just tm -> pure tm
  Nothing -> left (BadDomainLookup dom loc)

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

-- | Close the outermost level of variables
close :: GenesisTerm -> Domain -> GenesisTerm
close top sub = close' 0 top
  where close' ix body = case body of
          Computation pos neg -> Computation (closeVal pos ix)
                                             (closeCoval neg ix)
          Value v -> Value (closeVal v ix)
          Covalue cv -> Covalue (closeCoval cv ix)
          Bound i loc ->
            if i == ix
            then case domainLookup sub loc of
                   Just body' -> body'
                   Nothing -> error "failed variable lookup"
            else body
          o@(Oracle _) -> o

        closeVal :: GenesisValue -> Word32 -> GenesisValue
        closeVal v ix = case v of
          Sum loc subTm -> Sum loc (close' ix subTm)
          Product vec -> Product $ (\subTm -> close' ix subTm) <$> vec

        closeCoval :: GenesisCovalue -> Word32 -> GenesisCovalue
        closeCoval cv ix = case cv of
          Case vec -> Case $ (\subTm -> close' ix subTm) <$> vec
          Match subTm -> Match $ close' (ix + 1) subTm
