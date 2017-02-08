{-# language GADTs #-}

module Interplanetary.Eval where

import Interplanetary.Genesis
import Interplanetary.Meta

step :: GenesisTerm -> GenesisTerm
step v@(Value _) = v
step c@(Covalue _) = c

step (Computation (Sum pos body) (Case branches)) =
  case domainLookup branches pos of
    -- Substitute in the untagged term in the case rhs
    Just result -> close result (AtomicDomain body)
    Nothing -> error $ "failed lookup: " ++ show pos

-- Substitute all terms from the domain (destructured) in the body
step (Computation (Product subs) (Match body)) = close body subs

step (Splice tm) = splice tm
step (Quote tm) = quote tm
step e@(External _) = e

-- question: this is not a very informative way to signal stuck-ness. can we do
-- so without introducing more complexity to the language?
step var@(Bound _level _pos) = var -- we're stuck


-- | Close the outermost level of variables
close :: GenesisTerm
      -> Domain pos
      -> GenesisTerm
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

        closeVal :: GenesisValue a b -> Int -> GenesisValue a b
        closeVal v ix = case v of
          Sum loc subTm -> Sum loc (close' ix subTm)
          Product dom -> Product $ mapDomain (\subTm -> close' ix subTm) dom

        closeCoval :: GenesisCovalue a b -> Int -> GenesisCovalue a b
        closeCoval cv ix = case cv of
          Case dom -> Case $ mapDomain (\subTm -> close' ix subTm) dom
          Match subTm -> Match $ close' (ix + 1) subTm
