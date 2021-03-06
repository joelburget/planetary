{-# language Rank2Types #-}
module Planetary.Util
  ( Vector
  , Stack
  , todo
  , assertM
  , assert
  , strictZip
  , withState'
  , localState
  , ifNotJust
  , (??)
  , (<$$>)
  , (<&&>)
  , (<$$$>)
  , over2
  , uncurry3
  , traceDoc
  , traceDocM
  , traceText
  , traceTextM
  ) where

import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Newtype
import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Render.Terminal
import Data.Text (Text)
import qualified Data.Text.IO as Text
import System.IO.Unsafe (unsafePerformIO)

-- TODO change to Vector
type Vector a = [a]
type Stack a = [a]

todo :: String -> forall a. a
todo = error

assertM :: Bool -> Maybe ()
assertM valid = if valid then pure () else Nothing

assert :: MonadError e m => e -> Bool -> m ()
assert reason valid = if valid then pure () else throwError reason

strictZip :: MonadError e m => ([a] -> [b] -> e) -> [a] -> [b] -> m [(a, b)]
strictZip e as bs =
  if length as == length bs
  then pure (zip as bs)
  else throwError (e as bs)

-- TODO: this has to be a standard function
withState' :: MonadState s m => (s -> s) -> m a -> m a
withState' update action = do
  s <- get
  put (update s)
  result <- action
  put s
  pure result

-- | Run a state action and undo the state changes at the end.
localState :: MonadState s m => m a -> m a
{-# INLINE localState #-}
localState m = do
    s <- get
    x <- m
    put s
    return x

infix 0 ??

(??) :: MonadError e m => Maybe a -> e -> m a
(Just a) ?? _  = pure a
Nothing ?? err = throwError err

ifNotJust :: MonadError e m => e -> Maybe a -> m a
ifNotJust = flip (??)

infixl 4 <$$>

(<$$>) :: (Functor f, Functor g) => (a -> b) -> f (g a) -> f (g b)
(<$$>) = fmap . fmap

infixl 1 <&&>
(<&&>) :: (Functor f, Functor g) => f (g a) -> (a -> b) -> f (g b)
(<&&>) = flip (<$$>)

infixl 5 <$$$>

(<$$$>) :: (Functor f, Functor g, Functor h) => (a -> b) -> f (g (h a)) -> f (g (h b))
(<$$$>) = fmap . fmap . fmap

-- traverse2
--   :: (Traversable s, Traversable t, Applicative f)
--   => (a -> f b)
--   -> s (t a)
--   -> f (s (t b))
-- traverse2 = traverse . traverse

over2
  :: (Newtype n o, Newtype n' o')
  => (o -> n) -> (o -> o -> o') -> (n -> n -> n')
over2 _newtype f n1 n2 = pack (f (unpack n1) (unpack n2))

uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

{-# noinline traceDoc #-}
traceDoc :: Doc AnsiStyle -> a -> a
traceDoc doc expr = unsafePerformIO $ do
  putDoc doc
  return expr

traceDocM :: Applicative f => Doc AnsiStyle -> f ()
traceDocM doc = traceDoc doc $ pure ()

{-# noinline traceText #-}
traceText :: Text -> a -> a
traceText text expr = unsafePerformIO $ do
  Text.putStrLn text
  pure expr

traceTextM :: Applicative f => Text -> f ()
traceTextM text = traceText text $ pure ()
