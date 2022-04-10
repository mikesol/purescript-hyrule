module FRP.Event.Memoized
  ( Event
  , EventIO
  , create
  , makeEvent
  , subscribe
  , fromEvent
  , toEvent
  , module Class
  ) where

import Prelude

import Control.Alt (class Alt, alt)
import Control.Plus (class Plus, empty)
import FRP.Event.Memoize (class MemoizableEvent, isMemoized, unsafeMemoize)
import Data.Compactable (class Compactable, compact, separate)
import Data.Exists (Exists, mkExists, runExists)
import Data.Filterable (filter, filterMap, partition, partitionMap)
import Data.Foldable (foldl)
import Data.Profunctor (dimap)
import Effect (Effect)
import FRP.Event (class Filterable, fix, fold, keepLatest, sampleOn)
import FRP.Event as Event
import FRP.Event.Class (class Filterable, class IsEvent, biSampleOn, count, filterMap, fix, fold, folded, gate, gateBy, keepLatest, mapAccum, sampleOn, sampleOn_, withLast) as Class
import Safe.Coerce (coerce)

fromEvent :: Event.Event ~> Event
fromEvent = Event

toEvent :: Event ~> Event.Event
toEvent (Event e) = e

derive newtype instance memoizableMemoizableEvent :: MemoizableEvent Event

memoizeIfMemoized :: Array (Exists Event.Event) -> Event.Event ~> Event.Event
memoizeIfMemoized a e = if foldl (&&) true (map (runExists isMemoized) a) then unsafeMemoize e else e

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
-- |
-- | This flavor of event automatically memoizes event whose dependencies are memoized.
-- | In certain cases this can lead to substantial performmance gains.
-- | For better performance, though, you'll want to use `Event` and only memoize events
-- | that have a performance gain, as memoization will often speed stuff up on the whole
-- | but, for certain events, cause a slight performance degradation.
newtype Event a = Event (Event.Event a)

instance functorEvent :: Functor Event where
  map a (Event f) = Event (memoizeIfMemoized [ mkExists f ] (map a f))

instance compactableEvent :: Compactable Event where
  compact (Event f) = Event (memoizeIfMemoized [ mkExists f ] (compact f))
  separate (Event f) =
    let
      { left, right } = separate f
    in
      { left: Event $ memoizeIfMemoized [ mkExists f ] left
      , right: Event $ memoizeIfMemoized [ mkExists f ] right
      }

instance filterableEvent :: Filterable Event where
  partitionMap fn (Event f) =
    let
      { left, right } = partitionMap fn f
    in
      { left: Event $ memoizeIfMemoized [ mkExists f ] left
      , right: Event $ memoizeIfMemoized [ mkExists f ] right
      }
  partition fn (Event f) =
    let
      { yes, no } = partition fn f
    in
      { yes: Event $ memoizeIfMemoized [ mkExists f ] yes
      , no: Event $ memoizeIfMemoized [ mkExists f ] no
      }
  filterMap fn (Event f) = Event (memoizeIfMemoized [ mkExists f ] (filterMap fn f))
  filter fn (Event f) = Event (memoizeIfMemoized [ mkExists f ] (filter fn f))

instance altEvent :: Alt Event where
  alt (Event a) (Event b) = Event (memoizeIfMemoized [ mkExists a, mkExists b ] (alt a b))

instance plusEvent :: Plus Event where
  empty = Event (unsafeMemoize empty)

instance isEvent :: Class.IsEvent Event where
  fold abb (Event a) b = Event (memoizeIfMemoized [ mkExists a ] (fold abb a b))
  keepLatest (Event f) = Event (memoizeIfMemoized [ mkExists f ] (keepLatest (map (\i -> let Event e = i in e) f)))
  sampleOn (Event a) (Event ab) = Event (memoizeIfMemoized [ mkExists a, mkExists ab ] (sampleOn a ab))
  fix f =
    let
      io = f empty
    in
      Event
        ( memoizeIfMemoized [ mkExists (let Event i = io.input in i), mkExists (let Event o = io.output in o) ]
            (fix $ dimap Event coerce f)
        )
  bang = bang

bang :: forall a. a -> Event a
bang a =  (Event (unsafeMemoize (Event.bang a)))

-- | Subscribe to an `Event` by providing a callback.
-- |
-- | `subscribe` returns a canceller function.
subscribe
  :: forall a
   . Event a
  -> (a -> Effect Unit)
  -> Effect (Effect Unit)
subscribe (Event e) = Event.subscribe e

-- | Make an `Event` from a function which accepts a callback and returns an
-- | unsubscription function.
-- |
-- | Note: these events are _NOT_ memoized. To memoize them, you _MUST_ call
-- | memoize explicitly.
-- | Note: you probably want to use `create` instead, unless you need explicit
-- | control over unsubscription.
makeEvent
  :: forall a
   . ((a -> Effect Unit) -> Effect (Effect Unit))
  -> Event a
makeEvent = Event <<< Event.makeEvent

type EventIO a =
  { event :: Event a
  , push :: a -> Effect Unit
  }

-- | Create an event and a function which supplies a value to that event.
-- | Events created using create can be memoized.
create
  :: forall a
   . Effect (EventIO a)
create = Event.create <#> \i -> i { event = Event $ unsafeMemoize i.event }
