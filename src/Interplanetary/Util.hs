{-# language Rank2Types #-}
module Interplanetary.Util where

import Control.Monad.State.Strict
import Control.Monad.Except

-- TODO change to Vector
type Vector a = [a]
type Stack a = [a]

todo :: String -> forall a. a
todo = error

assertM :: Bool -> Maybe ()
assertM valid = if valid then pure () else Nothing

assert :: MonadError e m => e -> Bool -> m ()
assert reason valid = if valid then pure () else throwError reason

strictZip :: MonadError e m => e -> [a] -> [b] -> m [(a, b)]
strictZip e as bs =
  if length as == length bs
  then pure (zip as bs)
  else throwError e

-- TODO: this has to be a standard function
withState' :: MonadState s m => (s -> s) -> m a -> m a
withState' update action = do
  s <- get
  put (update s)
  result <- action
  put s
  pure result

infix 0 ??

(??) :: MonadError e m => Maybe a -> e -> m a
(Just a) ?? _  = pure a
Nothing ?? err = throwError err
