{-# language Rank2Types #-}
module Interplanetary.Util where

import Control.Monad.State.Strict
import Control.Monad.Except

-- TODO change to Vector
type Vector a = [a]
type Stack a = [a]

assertM :: Bool -> Maybe ()
assertM valid = if valid then pure () else Nothing

assert :: Monad m => e -> Bool -> ExceptT e m ()
assert reason valid = if valid then pure () else throwError reason

todo :: String -> forall a. a
todo = error

strictZip :: Vector a -> Vector b -> Maybe (Vector (a, b))
strictZip as bs = if length as == length bs then Just (zip as bs) else Nothing

-- TODO: this has to be a standard function
withState' :: MonadState s m => (s -> s) -> m a -> m a
withState' update action = do
  s <- get
  put (update s)
  result <- action
  put s
  pure result
