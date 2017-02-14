module Tests.Meta where

import Test.QuickCheck

-- Test that splice / quote define an isomorphism
-- * quote . splice = id
-- * spilce . quote = id

newtype Quoted = Quoted GenesisTerm

instance Arbitrary Quoted where

prop_inversion1 :: Quoted -> Bool
prop_inversion1 q = let Quoted tm = q in quote (splice tm) == tm

prop_inversion2 :: GenesisTerm -> Bool
prop_inversion2 tm = splice (quote tm) == tm
