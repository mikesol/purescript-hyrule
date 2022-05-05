module FRP.Event
  ( AnEvent
  , Event
  , EventIO
  , create
  , makeEvent
  , subscribe
  , bang
  , bus
  , memoize
  , module Class
  ) where

import Prelude

import Control.Alternative (class Alt, class Plus)
import Control.Monad.ST.Class (class MonadST, liftST)
import Control.Monad.ST.Internal as Ref
import Data.Array (deleteBy)
import Data.Compactable (class Compactable)
import Data.Either (Either(..), either, hush)
import Data.Filterable (class Filterable, filterMap)
import Data.Foldable (sequence_, traverse_)
import Data.Maybe (Maybe(..))
import Effect (Effect)
import FRP.Event.Class (class Filterable, class IsEvent, count, filterMap, fix, fold, folded, gate, gateBy, keepLatest, mapAccum, sampleOn, sampleOn_, withLast) as Class
import Unsafe.Reference (unsafeRefEq)

-- | An `Event` represents a collection of discrete occurrences with associated
-- | times. Conceptually, an `Event` is a (possibly-infinite) list of values-and-times:
-- |
-- | ```purescript
-- | type Event a = List { value :: a, time :: Time }
-- | ```
-- |
-- | Events are created from real events like timers or mouse clicks, and then
-- | combined using the various functions and instances provided in this module.
-- |
-- | Events are consumed by providing a callback using the `subscribe` function.
newtype AnEvent m a = AnEvent ((a -> m Unit) -> m (m Unit))
type Event a = AnEvent Effect a

instance functorEvent :: Functor (AnEvent m) where
  map f (AnEvent e) = AnEvent \k -> e (k <<< f)

instance compactableEvent :: Applicative m => Compactable (AnEvent m) where
  compact = filter identity
  separate xs =
    { left:
        filter
          ( case _ of
              Left x -> Just x
              Right _ -> Nothing
          )
          xs
    , right:
        filter
          ( case _ of
              Right x -> Just x
              Left _ -> Nothing
          )
          xs
    }

filter' :: forall m a. Applicative m => (a → Boolean) → AnEvent m a → AnEvent m a
filter' f =
  filter
    ( \a -> case f a of
        true -> Just a
        false -> Nothing
    )

instance filterableEvent :: Applicative m => Filterable (AnEvent m) where
  filter = filter'
  filterMap = filter
  partition p xs = { yes: filter' p xs, no: filter' (not <<< p) xs }
  partitionMap f xs =
    { left: filterMap (either Just (const Nothing) <<< f) xs
    , right: filterMap (hush <<< f) xs
    }

instance altEvent :: Applicative m => Alt (AnEvent m) where
  alt (AnEvent f) (AnEvent g) =
    AnEvent \k -> ado
      c1 <- f k
      c2 <- g k
      in (c1 *> c2)

instance plusEvent :: Applicative m => Plus (AnEvent m) where
  empty = AnEvent \_ -> pure (pure unit)

instance eventIsEvent :: MonadST s m => Class.IsEvent (AnEvent m) where
  fold = fold
  keepLatest = keepLatest
  sampleOn = sampleOn
  fix = fix
  bang = bang

-- | Fold over values received from some `Event`, creating a new `Event`.
fold :: forall m s a b. MonadST s m => (a -> b -> b) -> AnEvent m a -> b -> AnEvent m b
fold f (AnEvent e) b =
  AnEvent \k -> do
    result <- liftST (Ref.new b)
    e \a -> liftST (Ref.modify (f a) result) >>= k

-- | Create an `Event` which only fires when a predicate holds.
filter :: forall m s a b. Applicative m => (a -> Maybe b) -> AnEvent m a -> AnEvent m b
filter p (AnEvent e) =
  AnEvent \k ->
    e \a -> case p a of
      Just y -> k y
      Nothing -> pure unit

-- | Create an `Event` which samples the latest values from the first event
-- | at the times when the second event fires.
sampleOn :: forall m s a b. MonadST s m => Applicative m => AnEvent m a -> AnEvent m (a -> b) -> AnEvent m b
sampleOn (AnEvent e1) (AnEvent e2) =
  AnEvent \k -> do
    latest <- liftST $ Ref.new Nothing
    c1 <-
      e1 \a -> do
        liftST $ void $ Ref.write (Just a) latest
    c2 <-
      e2 \f -> do
        (liftST $ Ref.read latest) >>= traverse_ (k <<< f)
    pure (c1 *> c2)

-- | Flatten a nested `Event`, reporting values only from the most recent
-- | inner `Event`.
keepLatest :: forall m s a. MonadST s m =>  AnEvent m (AnEvent m a) -> AnEvent m a
keepLatest (AnEvent e) =
  AnEvent \k -> do
    cancelInner <- liftST $ Ref.new Nothing
    cancelOuter <-
      e \inner -> do
        (liftST $ Ref.read cancelInner) >>= sequence_
        c <- subscribe inner k
        liftST $ void $ Ref.write (Just c) cancelInner
    pure do
      (liftST $ Ref.read cancelInner) >>= sequence_
      cancelOuter

-- | Compute a fixed point
fix :: forall m s i o. MonadST s m => Monad m => (AnEvent m i -> { input :: AnEvent m i, output :: AnEvent m o }) -> AnEvent m o
fix f =
  AnEvent \k -> do
    { event, push } <- create
    let { input, output } = f event
    c1 <- subscribe input push
    c2 <- subscribe output k
    pure (c1 *> c2)

-- | Subscribe to an `Event` by providing a callback.
-- |
-- | `subscribe` returns a canceller function.
subscribe
  :: forall m a
   . AnEvent m a
  -> (a -> m Unit)
  -> m (m Unit)
subscribe (AnEvent e) k = e k

-- | Make an `Event` from a function which accepts a callback and returns an
-- | unsubscription function.
-- |
-- | Note: you probably want to use `create` instead, unless you need explicit
-- | control over unsubscription.
makeEvent
  :: forall a
   . ((a -> Effect Unit) -> Effect (Effect Unit))
  -> Event a
makeEvent = AnEvent

type EventIO a =
  { event :: Event a
  , push :: a -> Effect Unit
  }

type AnEventIO m a =
  { event :: AnEvent m a
  , push :: a -> m Unit
  }
-- | Create an event and a function which supplies a value to that event.
create
  :: forall m s a
   . MonadST s m => m (AnEventIO m a)
create = do
  subscribers <- liftST $ Ref.new []
  pure
    { event:
        AnEvent \k -> do
          _ <- liftST $ Ref.modify (_ <> [ k ]) subscribers
          pure do
            _ <- liftST $ Ref.modify (deleteBy unsafeRefEq k) subscribers
            pure unit
    , push:
        \a -> do
          (liftST $ (Ref.read subscribers)) >>= traverse_ \k -> k a
    }

bang :: forall m a. Applicative m => a -> AnEvent m a
bang a =
  AnEvent \k -> ado
    k a
    in pure unit

bus :: forall r a. ((a -> Effect Unit) -> Event a -> r) -> Event r
bus f = makeEvent \k -> do
  { push, event } <- create
  k (f push event)
  pure (pure unit)

memoize :: forall r a. Event a -> (Event a -> r) -> Event r
memoize e f = makeEvent \k -> do
  { push, event } <- create
  k (f event)
  subscribe e push