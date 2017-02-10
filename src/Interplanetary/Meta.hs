{-# language OverloadedStrings #-}
{-# language OverloadedLists #-}
{-# language GADTs #-}
{-# language PatternSynonyms #-}
{-# language ViewPatterns #-}
{-# language Rank2Types #-}

module Interplanetary.Meta where

import qualified Data.Vector as V
import Data.Vector (Vector)

import Interplanetary.Genesis

todo :: forall a. a
todo = error "TODO"
pattern V2 :: a -> a -> Vector a
pattern V2 a b <- (V.toList -> [a, b]) where
  V2 a b = V.fromList [a, b]

pattern Vx :: [a] -> Vector a
pattern Vx lst <- (V.toList -> lst) where
  Vx lst = V.fromList lst

pattern SumRep :: GenesisTerm -> GenesisTerm -> GenesisTerm
pattern SumRep a b = Sum' (Name "Sum") (Product' (PositionalDomain (V2 a b)))

pattern ComputationRep :: GenesisTerm -> GenesisTerm -> GenesisTerm
pattern ComputationRep valrep covalrep = Sum'
  (Name "Computation")
  (Product' (PositionalDomain (V2 valrep covalrep)))

pattern BoundRep :: GenesisTerm -> GenesisTerm -> GenesisTerm
pattern BoundRep a b = Sum'
  (Name "Bound")
  (Product' (PositionalDomain (V2 a b)))

pattern QuoteRep :: GenesisTerm -> GenesisTerm
pattern QuoteRep a = Sum' (Name "Quote") a

pattern SpliceRep :: GenesisTerm -> GenesisTerm
pattern SpliceRep a = Sum' (Name "Splice") a

pattern OracleRep :: GenesisTerm -> GenesisTerm
pattern OracleRep a = Sum' (Name "Oracle") a

pattern ProductRep :: GenesisTerm -> GenesisTerm
pattern ProductRep a = Sum' (Name "Product") a

pattern CaseRep :: GenesisTerm -> GenesisTerm
pattern CaseRep a = Sum' (Name "Case") a

pattern MatchRep :: GenesisTerm -> GenesisTerm
pattern MatchRep a = Sum' (Name "Match") a

{-
-- | Define the term syntax in the term syntax.
--
-- Where do we use this?
termSyntax :: GenesisTerm
termSyntax = Product' $ nominalDomain'
  -- TODO this smells wrong
  [ ("Computation", Product' (PositionalDomain [valueSyntax, covalueSyntax]))
  , ("Value", valueSyntax)
  , ("Covalue", covalueSyntax)
  , ("Bound", todo)

  , ("Quote", todo)
  , ("Splice", todo)
  , ("Oracle", todo)
  ]

valueSyntax :: GenesisTerm
valueSyntax = Product' $ nominalDomain'
  [ ("Sum", todo)
  , ("Product", todo)
  ]

covalueSyntax :: GenesisTerm
covalueSyntax = Product' $ nominalDomain'
  [ ("Case", todo)
  , ("Match", todo)
  ]
-}

-- TODO: should this be an external?
unit :: GenesisTerm
unit = Product' (PositionalDomain [])

-- | Transfor an expression into the representation of that epxression
--
-- When do you actually need this in the genesis language? Well, our goal is to
-- *enhance* the language, not create new ones from scratch. Indicating we want
-- to borrow from the base language.
--
-- `splice . quote` of course results in the original term.
quote :: GenesisTerm -> GenesisTerm
quote tm = case tm of
  Computation val coval -> ComputationRep (quoteVal val) (quoteCoval coval)
  Value val -> quoteVal val
  Covalue coval -> quoteCoval coval
  Bound level pos -> BoundRep (Oracle (todo level)) (quoteLoc pos)

  Quote q -> QuoteRep (quote q)
  Splice s -> SpliceRep (quote s)
  Oracle hash -> OracleRep (quoteMultiHash hash)

quoteVal :: GenesisValue a b -> GenesisTerm
quoteVal (Sum loc tm) = SumRep (quoteLoc loc) (quote tm)
quoteVal (Product dom) = ProductRep (quoteDom dom)

quoteCoval :: GenesisCovalue a b -> GenesisTerm
quoteCoval (Case dom) = CaseRep (quoteDom dom)
quoteCoval (Match tm) = MatchRep (quote tm)

quoteLoc :: Location pos -> GenesisTerm
quoteLoc = todo

quoteDom :: Domain pos -> GenesisTerm
quoteDom = todo

quoteMultiHash :: MultiHash -> GenesisTerm
quoteMultiHash = todo

-- | Transfer the representation of a term to a term
splice :: GenesisTerm -> GenesisTerm
splice (SumRep tagRep tm) = Sum' (spliceTag tagRep) (splice tm)
splice (ProductRep dom) = Product' (spliceDom dom)
splice (CaseRep dom) = Case' (spliceDom dom)
splice (MatchRep tm) = Match' (splice tm) -- XXX open level
splice (QuoteRep tm) = todo
splice (SpliceRep tm) = todo
splice (OracleRep tm) = todo
splice problematic = error "problematic"

spliceTag :: GenesisTerm -> Location pos
spliceTag = todo

spliceDom :: GenesisTerm -> Domain pos
spliceDom = todo
