module Test.Main where

import Prelude

import Control.Alt ((<|>))
import Control.Monad.ST (ST)
import Control.Monad.ST.Class (liftST)
import Control.Monad.ST.Ref (STRef)
import Control.Monad.ST.Ref as STRef
import Control.Plus (empty)
import Data.Array (length, replicate, (..))
import Data.Array as Array
import Data.Filterable (filter)
import Data.Foldable (oneOf, oneOfMap, sequence_)
import Data.FunctorWithIndex (mapWithIndex)
import Data.JSDate (getTime, now)
import Data.Maybe (Maybe(..))
import Data.Newtype (under)
import Data.Op (Op(..))
import Data.Traversable (foldr, for_, sequence)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested ((/\))
import Debug (spy)
import Effect (Effect)
import Effect.Aff (Milliseconds(..), delay, launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import FRP.Event (justNone, justOne, makeEvent, memoize, merge, subscribe)
import FRP.Event as Event
import FRP.Event.Class (fold, gate, keepLatest, once, sampleOnRight)
import FRP.Event.Time (throttle, withTime)
import FRP.Poll as OptimizedPoll
import FRP.Poll.Unoptimized as UnoptimizedPoll
import Foreign.Object.ST as STObject
import Test.Spec (describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Console (write)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (runSpec)

modify__ :: forall a r. (a -> a) -> STRef r a -> ST r Unit
modify__ a b = void $ STRef.modify a b

fresh :: forall a r. a -> ST r (STRef r a)
fresh = STRef.new

-- Because of limitations in how polymorphism works in PureScript,
-- every test needs to have the same type for the pusher and output.
-- For most tests that's `Int` and `Int`, but for a couple, the input type
-- is `Unit` and the output type is somethign different. So we
-- need new suites for those.
suite1 name { setup, prime, create, toEvent, underTest } = do
  describe name do
    it "should do simple stuff" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      u1 <- subscribe (toEvent (underTest testing) ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push 0
      v <- liftST $ STRef.read r
      v `shouldEqual` [ 0 ]
      u2 <- subscribe (toEvent (underTest testing) ep) \i ->
        liftST $ void $ STRef.modify (Array.cons (negate i)) r
      v' <- liftST $ STRef.read r
      v' `shouldEqual` [ 0 ]
      prime ep
      testing.push 1
      v'' <- liftST $ STRef.read r
      v'' `shouldEqual` [ -1, 1, 0 ]
      (u1 *> u2)
    it "should do a lot more complex addition" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        testAddition = do
          let
            add1 = map (add 1) (underTest testing)
            add2 = map (add 2) add1
            add3 = map (add 3) add2
            add4 = map (add 4) add3
          add1 <|> add4
      u <- subscribe (toEvent testAddition ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push 0
      v <- liftST $ STRef.read r
      v `shouldEqual` [ 10, 1 ]
      u
    it "should handle alt" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        testAlt = do
          let
            add1 = (map (add 1) (underTest testing))
            add2 = map (add 2) add1
            add3 = map (add 3) add2
            add4 = map (add 4) add3
            altr = add1 <|> add2 <|> empty <|> add4 <|> empty
          add1 <|> altr
      u <- subscribe (toEvent testAlt ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push 0
      v <- liftST $ STRef.read r
      v `shouldEqual` [ 10, 3, 1, 1 ]
      u
    it "should handle filter 1" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        filtered = do
          let
            add1 = map (add 1) (underTest testing)
            add2 = map (add 2) add1
            add3 = map (add 3) add2
            add4 = map (add 4) add3
            altr = add1 <|> add2 <|> empty <|> add4 <|> empty
            fm = (filter (_ < 5) altr)
          add1 <|> fm
      u <- subscribe (toEvent filtered ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push 0
      v <- liftST $ STRef.read r
      v `shouldEqual` [ 3, 1, 1 ]
      u
    it "should handle filter 2" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let add1 = (map (add 1) (underTest testing))
      let add2 = map (add 2) add1
      let add3 = map (add 3) add2
      let add4 = map (add 4) add3
      let altr = add1 <|> add2 <|> empty <|> add4 <|> empty
      let fm = (filter (_ > 5) altr)
      u <- subscribe (toEvent (add1 <|> fm) ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push 0
      v <- liftST $ STRef.read r
      v `shouldEqual` [ 10, 1 ]
      u
    it "should sampleOnRight correctly" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing0 <- liftST create
      testing1 <- liftST create
      let toTest = sampleOnRight (underTest testing0) (add <$> (underTest testing1))
      u <- subscribe (toEvent toTest ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      -- noop
      testing1.push 1
      -- noop
      testing0.push 3
      -- 45
      testing1.push 42
      -- 104
      testing1.push 101
      -- no op
      testing0.push 42
      -- 50
      testing1.push 8
      -- 51
      testing1.push 9
      v <- liftST $ STRef.read r
      v `shouldEqual` [ 51, 50, 104, 45 ]
      u
    it "should keepLatest" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing0 <- liftST create
      testing1 <- liftST create
      let toTest = keepLatest (underTest testing0 $> underTest testing1)
      u <- subscribe (toEvent toTest ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing0.push 42
      testing1.push 3
      testing1.push 4
      testing0.push 42
      testing1.push 5
      testing1.push 6
      v <- liftST $ STRef.read r
      v `shouldEqual` [ 6, 5, 4, 3 ]
      u
  it "should keep itself when keepLatest is used" $ liftEffect do
    r <- liftST $ STRef.new []
    ep <- liftST setup
    testing <- liftST $ create
    let tested = underTest testing
    u1 <- subscribe (toEvent (keepLatest (tested $> tested)) ep) \i -> do
      liftST $ void $ STRef.modify (Array.cons i) r
    prime ep
    testing.push 0
    testing.push 1
    testing.push 42
    v <- liftST $ STRef.read r
    v `shouldEqual` [ 42, 1, 0 ]
    u1
  it "always applies updates from left to right, emitting at each update" $ liftEffect do
    r <- liftST $ STRef.new []
    ep <- liftST setup
    testing <- liftST create
    u <- Event.subscribe (toEvent (let x = (underTest testing) in (map add x) <*> x) ep) \i ->
      liftST $ void $ STRef.modify (flip Array.snoc i) r
    prime ep
    testing.push 1
    testing.push 2
    o <- liftST $ STRef.read r
    o `shouldEqual` [ 2, 3, 4 ]
    u
  it "always applies multiple updates from left to right, emitting at each update" $ liftEffect do
    r <- liftST $ STRef.new []
    ep <- liftST setup
    testing <- liftST create
    let addSixNums x y z a b c = x + y + z + a + b + c
    u <- Event.subscribe (toEvent (let x = (underTest testing) in addSixNums <$> x <*> x <*> x <*> x <*> x <*> x) ep) \i ->
      liftST $ void $ STRef.modify (flip Array.snoc i) r
    prime ep
    testing.push 1
    testing.push 2
    o <- liftST $ STRef.read r
    o `shouldEqual` [ 6, 7, 8, 9, 10, 11, 12 ]
    u

suite2 name { setup, prime, create, toEvent, underTest, muxEvent } = do
  describe name do
    it "should handle fold 1" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        event' = do
          let foldy = (fold (\b _ -> b + 1) 0 (underTest testing))
          let add2 = map (add 2) foldy
          let add3 = map (add 3) add2
          let add4 = map (add 4) add3
          let altr = foldy <|> add2 <|> empty <|> add4 <|> empty
          let fm = (filter (_ > 5) altr)
          foldy <|> fm
      u <- subscribe (toEvent event' ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push unit
      liftST (STRef.read r) >>= shouldEqual [ 10, 1 ]
      liftST $ void $ STRef.write [] r
      testing.push unit
      liftST (STRef.read r) >>= shouldEqual [ 11, 2 ]
      liftST $ void $ STRef.write [] r
      testing.push unit
      liftST (STRef.read r) >>= shouldEqual [ 12, 3 ]
      u
    it "should handle foldObj" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        event' = do
          let
            go :: forall r. STObject.STObject r Int -> Unit -> ST r Int
            go obj _ = do
              x <- STObject.peek "foo" obj
              case x of
                Nothing -> do
                  void $ STObject.poke "foo" 1 obj
                  pure 1
                Just x -> do
                  let _ = spy "OHHI" x
                  void $ STObject.poke "foo" (x + 1) obj
                  pure (x + 1)
          let foldy = (muxEvent (Event.foldObj go) (underTest testing))
          let add2 = map (add 2) foldy
          let add3 = map (add 3) add2
          let add4 = map (add 4) add3
          let altr = foldy <|> add2 <|> empty <|> add4 <|> empty
          let fm = (filter (_ > 5) altr)
          foldy <|> fm
      u <- subscribe (toEvent event' ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push unit
      liftST (STRef.read r) >>= shouldEqual [ 10, 1 ]
      liftST $ void $ STRef.write [] r
      testing.push unit
      liftST (STRef.read r) >>= shouldEqual [ 11, 2 ]
      liftST $ void $ STRef.write [] r
      testing.push unit
      liftST (STRef.read r) >>= shouldEqual [ 12, 3 ]
      u

suite3 name { setup, prime, create, toEvent, underTest } = do
  describe name do
    it "should handle fold 2" do
      liftEffect do
        r <- liftST $ STRef.new []
        ep <- liftST setup
        testing <- liftST create
        let
          event' = do
            let add1 = map (add 1) (underTest testing)
            let add2 = map (add 2) add1
            let add3 = map (add 3) add2
            let foldy = fold (\b a -> a + b) 0 add3
            let add4 = map (add 4) add3
            let altr = foldy <|> add2 <|> empty <|> add4 <|> empty
            sampleOnRight add2 (map (\a b -> b /\ a) (filter (_ > 5) altr))
        u <- subscribe (toEvent event' ep) \i ->
          liftST $ void $ STRef.modify (Array.cons i) r
        prime ep
        testing.push 0
        liftST (STRef.read r) >>= shouldEqual [ Tuple 3 10, Tuple 3 6 ]
        liftST $ void $ STRef.write [] r
        testing.push 0
        liftST (STRef.read r) >>= shouldEqual [ Tuple 3 10, Tuple 3 12 ]
        liftST $ void $ STRef.write [] r
        testing.push 0
        liftST (STRef.read r) >>= shouldEqual [ Tuple 3 10, Tuple 3 18 ]
        u

suite4 name { setup, prime, create, toEvent, underTest } = do
  describe name do
    it "should ignore left pushes on initial event but respond to both right pushes" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        e e' = Tuple <$> (e' $> 1 <|> e' $> 2) <*> (e' $> 3 <|> e' $> 4)
      u <- subscribe (toEvent (e (underTest testing)) ep) \i ->
        liftST $ void $ STRef.modify (flip Array.snoc i) r
      prime ep
      testing.push unit
      liftST (STRef.read r) >>= \y -> y `shouldEqual` [ Tuple 2 3, Tuple 2 4 ]
      u

suite5 name { setup, prime, create, toEvent, underTest } = do
  describe name do
    it "respects both sides of application" $ liftEffect do
      testing <- liftST create
      ep <- liftST setup
      rf0 <- liftST $ STRef.new ""
      rf1 <- liftST $ STRef.new ""
      let tested = underTest testing
      u1 <- Event.subscribe (toEvent ((append <$> (once tested $> "a")) <*> tested) ep) (liftST <<< void <<< flip STRef.write rf0)
      u2 <- Event.subscribe (toEvent ((append <$> tested) <*> (once tested $> "b")) ep) (liftST <<< void <<< flip STRef.write rf1)
      prime ep
      testing.push "c"
      rf0' <- liftST $ STRef.read rf0
      rf1' <- liftST $ STRef.read rf1
      rf0' `shouldEqual` "ac"
      rf1' `shouldEqual` "cb"
      u1 *> u2

suite6 name { setup, prime, create, toEvent, underTest } = do
  describe name do
    it "respects both sides of application" $ liftEffect do
      ep <- liftST setup
      testing <- liftST create
      rf0 <- liftST $ STRef.new ""
      rf1 <- liftST $ STRef.new ""
      let event = underTest testing
      void $ Event.subscribe (toEvent ((append <$> (once event $> "a")) <*> event) ep) (liftST <<< void <<< flip STRef.write rf0)
      void $ Event.subscribe (toEvent ((append <$> event) <*> (once event $> "b")) ep) (liftST <<< void <<< flip STRef.write rf1)
      prime ep
      testing.push "c"
      rf0' <- liftST $ STRef.read rf0
      rf1' <- liftST $ STRef.read rf1
      rf0' `shouldEqual` "ac"
      rf1' `shouldEqual` "cb"

suite7 name { setup, prime, create, mailbox, toEvent, underTest } = do
  it "should mailbox" $ liftEffect do
    r <- liftST $ STRef.new []
    ep <- liftST setup
    e <- liftST mailbox
    let event = underTest e
    u <- Event.subscribe (toEvent (event 3 <|> event 4) ep) \i ->
      liftST $ void $ STRef.modify (Array.cons i) r
    do
      prime ep
      e.push { address: 42, payload: true }
      e.push { address: 43, payload: true }
      e.push { address: 44, payload: true }
      e.push { address: 3, payload: true } --
      e.push { address: 42, payload: false }
      e.push { address: 43, payload: true }
      e.push { address: 43, payload: false }
      e.push { address: 4, payload: false } --
      e.push { address: 42, payload: false }
      e.push { address: 43, payload: true }
      e.push { address: 3, payload: false } --
      e.push { address: 101, payload: true }
    o <- liftST $ STRef.read r
    o `shouldEqual` [ false, false, true ]
    u

suite8 name { setup, prime, create, toEvent, underTest } = do
  describe name do
    it "should handle inside of fold 1" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        event' = sampleOnRight ((once (underTest testing) $> 0)) ((flip add) <$> (underTest testing))
      u <- subscribe (toEvent event' ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push 1
      liftST (STRef.read r) >>= shouldEqual [ 1 ]
      liftST $ void $ STRef.write [] r
      testing.push 55
      liftST (STRef.read r) >>= shouldEqual [ 55 ]
      liftST $ void $ STRef.write [] r
      testing.push 89
      liftST (STRef.read r) >>= shouldEqual [ 89 ]
      u
    it "should handle inside of fold 2" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        event' = sampleOnRight ((once (underTest testing) $> 0)) (oneOfMap (\x -> (add x >>> add) <$> (underTest testing)) [ 4, 5, 6, 7 ])
      u <- subscribe (toEvent event' ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push 1
      liftST (STRef.read r) >>= shouldEqual [ 8, 7, 6, 5 ]
      liftST $ void $ STRef.write [] r
      testing.push 55
      liftST (STRef.read r) >>= shouldEqual [ 62, 61, 60, 59 ]
      liftST $ void $ STRef.write [] r
      testing.push 89
      liftST (STRef.read r) >>= shouldEqual [ 96, 95, 94, 93 ]
      u
    it "should handle UnoptimizedPoll.poll fold 1" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        event' = fold (\b a -> b + a) 0 ((pure 5) <|> underTest testing)
      u <- subscribe (toEvent event' ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push 1
      liftST (STRef.read r) >>= shouldEqual [ 6, 5 ]
      liftST $ void $ STRef.write [] r
      testing.push 55
      liftST (STRef.read r) >>= shouldEqual [ 61 ]
      liftST $ void $ STRef.write [] r
      testing.push 89
      liftST (STRef.read r) >>= shouldEqual [ 150 ]
      u
    it "should handle UnoptimizedPoll.poll fold 2" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing <- liftST create
      let
        event' = fold (\b a -> b + a) 0 (oneOfMap pure [ 4, 5, 6 ] <|> underTest testing)
      u <- subscribe (toEvent event' ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing.push 1
      liftST (STRef.read r) >>= shouldEqual [ 16, 15, 9, 4 ]
      liftST $ void $ STRef.write [] r
      testing.push 55
      liftST (STRef.read r) >>= shouldEqual [ 71 ]
      liftST $ void $ STRef.write [] r
      testing.push 89
      liftST (STRef.read r) >>= shouldEqual [ 160 ]
      u

suite9 name { setup, prime, create, toEvent, underTest } = do
  describe name do
    it "should sampleOnRight correctly with pure" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing0 <- liftST create
      testing1 <- liftST create
      let toTest = sampleOnRight (underTest testing0) (oneOf (replicate 3 (add <$> (underTest testing1))))
      u <- subscribe (toEvent toTest ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      -- noop
      testing1.push 1
      -- noop
      testing0.push 3
      -- 45
      testing1.push 42
      -- 104
      testing1.push 101
      -- no op
      testing0.push 42
      -- 50
      testing1.push 8
      -- 51
      testing1.push 9
      v <- liftST $ STRef.read r
      v `shouldEqual` ([ 51, 50, 104, 45 ] >>= replicate 3)
      u

suite10 name { setup, prime, create, toEvent, underTest } = do
  describe name do
    it "should mapWithIndex" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing0 <- liftST create
      let toTest = mapWithIndex Tuple (pure 42 <|> underTest testing0)
      u <- subscribe (toEvent toTest ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      -- noop
      testing0.push 8
      -- noop
      testing0.push 15
      v <- liftST $ STRef.read r
      v `shouldEqual` (Array.reverse [ Tuple 0 42, Tuple 1 8, Tuple 2 15 ])
      u

suite11 name { setup, prime, create0, create1, toEvent, underTest } = do
  describe name do
    it "should gate" $ liftEffect do
      r <- liftST $ STRef.new []
      ep <- liftST setup
      testing0 <- liftST create0
      testing1 <- liftST create1
      let toTest = uncurry gate (underTest testing0 testing1)
      u <- subscribe (toEvent toTest ep) \i ->
        liftST $ void $ STRef.modify (Array.cons i) r
      prime ep
      testing0.push true
      testing1.push 1
      testing1.push 2
      testing0.push false
      testing1.push 3
      v <- liftST $ STRef.read r
      v `shouldEqual` (Array.reverse [ 1, 2 ])
      u

main :: Effect Unit
main = do
  launchAff_
    $ runSpec [ consoleReporter ] do
        suite1 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite1 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite1 "Event"
          { setup: pure unit
          , prime: pure
          , create: Event.create
          , toEvent: \e _ -> e
          , underTest: \testing -> testing.event
          }
        suite2 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          , muxEvent: UnoptimizedPoll.dredge
          }
        suite2 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          , muxEvent: OptimizedPoll.dredge
          }
        suite2 "Event"
          { setup: pure unit
          , prime: pure
          , create: Event.create
          , toEvent: \e _ -> e
          , underTest: \testing -> testing.event
          , muxEvent: identity
          }
        suite3 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite3 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite3 "Event"
          { setup: pure unit
          , prime: pure
          , create: Event.create
          , toEvent: \e _ -> e
          , underTest: \testing -> testing.event
          }
        suite4 "UnoptimizedPoll"
          { setup: Event.create
          , desc: "should distribute apply to all behaviors"
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite4 "OptimizedPoll"
          { setup: Event.create
          , desc: "should distribute apply to all behaviors"
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite4 "Event"
          { setup: pure unit
          , desc: "should ignore left pushes on initial event but respond to both right pushes"
          , prime: pure
          , create: Event.create
          , toEvent: \e _ -> e
          , underTest: \testing -> testing.event
          }
        suite5 "Event"
          { setup: pure unit
          , prime: pure
          , create: Event.create
          , toEvent: \e _ -> e
          , underTest: \testing -> testing.event
          }
        suite5 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite5 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite6 "Event"
          { setup: pure unit
          , prime: pure
          , create: Event.create
          , toEvent: \e _ -> e
          , underTest: \testing -> testing.event
          }
        suite6 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite6 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite7 "Event"
          { setup: pure unit
          , prime: pure
          , create: Event.create
          , mailbox: Event.mailbox
          , toEvent: \e _ -> e
          , underTest: \testing -> testing.event
          }
        suite7 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , mailbox: UnoptimizedPoll.mailbox
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite7 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , mailbox: UnoptimizedPoll.mailbox
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite8 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite8 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite9 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite9 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite10 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite10 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing -> testing.poll
          }
        suite11 "UnoptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create0: UnoptimizedPoll.create
          , create1: UnoptimizedPoll.create
          , toEvent: \b ep -> UnoptimizedPoll.sample_ b ep.event
          , underTest: \testing0 testing1 -> Tuple testing0.poll testing1.poll
          }
        suite11 "OptimizedPoll"
          { setup: Event.create
          , prime: \ep -> ep.push unit
          , create0: OptimizedPoll.create
          , create1: OptimizedPoll.create
          , toEvent: \b ep -> OptimizedPoll.sample_ b ep.event
          , underTest: \testing0 testing1 -> Tuple testing0.poll testing1.poll
          }
        suite11 "Event"
          { setup: pure unit
          , prime: pure
          , create0: Event.create
          , create1: Event.create
          , toEvent: \e _ -> e
          , underTest: \testing0 testing1 -> Tuple testing0.event testing1.event
          }
        describe "Unique to Poll" do
          it "should obliterate purity when on a rant" $ liftEffect do
            { event, push } <- liftST $ Event.create
            rf <- liftEffect $ Ref.new []
            unsub <- Event.subscribe (UnoptimizedPoll.sample_ (pure 42 :: UnoptimizedPoll.Poll Int) event) (\i -> Ref.modify_ (Array.cons i) rf)
            liftEffect do
              push unit
              o <- Ref.read rf
              o `shouldEqual` [ 42 ]
              unsub
              Ref.write [] rf
            ranting <- liftST $ UnoptimizedPoll.rant (pure 42)
            for_ (0 .. 1) \_ -> do
              unsub2 <- Event.subscribe (UnoptimizedPoll.sample_ ranting.poll event) (\i -> Ref.modify_ (Array.cons i) rf)
              liftEffect do
                push unit
                o <- Ref.read rf
                o `shouldEqual` []
                unsub2
                Ref.write [] rf
          it "should mix together UnoptimizedPoll.polling and purity" $ liftEffect do
            { event, push } <- liftST Event.create
            rf <- liftEffect $ Ref.new []
            pl <- liftST UnoptimizedPoll.create
            for_ (0 .. 1) \_ -> do
              unsub <- Event.subscribe (UnoptimizedPoll.sample_ (pure 42 <|> pure 42 <|> pl.poll) event) (\i -> Ref.modify_ (Array.cons i) rf)
              liftEffect do
                push unit
                o <- Ref.read rf
                o `shouldEqual` [ 42, 42 ]
                pl.push 43
                oo <- Ref.read rf
                oo `shouldEqual` [ 43, 42, 42 ]
                unsub
                Ref.write [] rf
          it "should give canned responses and hang up on UnoptimizedPoll.deflect" $ liftEffect do
            { event, push } <- liftST Event.create
            rf <- liftEffect $ Ref.new []
            pl <- liftST UnoptimizedPoll.create
            unsub <- Event.subscribe (UnoptimizedPoll.sample_ (pure 42 <|> pure 42 <|> pl.poll) event) (\i -> Ref.modify_ (Array.cons i) rf)
            liftEffect do
              push unit
              o <- Ref.read rf
              o `shouldEqual` [ 42, 42 ]
              pl.push 43
              oo <- Ref.read rf
              oo `shouldEqual` [ 43, 42, 42 ]
              unsub
              Ref.write [] rf
            deflecting <- liftST $ UnoptimizedPoll.deflect (pure 42 <|> pure 42 <|> pl.poll)
            for_ (0 .. 1) \_ -> do
              unsub2 <- Event.subscribe (UnoptimizedPoll.sample_ deflecting event) (\i -> Ref.modify_ (Array.cons i) rf)
              liftEffect do
                push unit
                o <- Ref.read rf
                o `shouldEqual` [ 42, 42 ]
                pl.push 43
                oo <- Ref.read rf
                -- UnoptimizedPoll.deflected, so ignores incoming stuff
                oo `shouldEqual` [ 42, 42 ]
                unsub2
                Ref.write [] rf
          it "should have a fixed point with an initial value" $ liftEffect do
            { event, push } <- liftST $ Event.create
            rf <- liftEffect $ Ref.new []
            unsub <- Event.subscribe (UnoptimizedPoll.sample_ (UnoptimizedPoll.fixB 0 (map (add 1))) event) (\i -> Ref.modify_ (Array.cons i) rf)
            liftEffect do
              push unit
              push unit
              push unit
              push unit
              o <- Ref.read rf
              o `shouldEqual` [ 4, 3, 2, 1 ]
              unsub
          it "should switch" $ liftEffect do
            r <- liftST $ STRef.new []
            switchDriver <- liftST $ Event.create
            poller <- liftST $ Event.create
            u <- subscribe (UnoptimizedPoll.sample_ (UnoptimizedPoll.switcher empty switchDriver.event) poller.event) \i ->
              liftST $ void $ STRef.modify (Array.cons i) r
            poller.push unit
            switchDriver.push (pure 42)
            poller.push unit
            poller.push unit
            switchDriver.push (pure 43)
            poller.push unit
            switchDriver.push (pure 44)
            switchDriver.push (pure 45)
            poller.push unit
            poller.push unit
            v <- liftST $ STRef.read r
            v `shouldEqual` [ 45, 45, 43, 42, 42 ]
            u

          it "should UnoptimizedPoll.gate when UnoptimizedPoll.gate is used" $ liftEffect do
            eio <- liftST $ Event.create
            r <- liftST $ STRef.new false
            n <- liftST $ STRef.new 0
            let b = UnoptimizedPoll.stRefToPoll r
            _ <- Event.subscribe (UnoptimizedPoll.gate b eio.event) \_ ->
              liftST $ void $ STRef.modify (add 1) n
            do
              eio.push unit
              eio.push unit
            liftST $ void $ STRef.write true r
            do
              eio.push unit
              eio.push unit
              eio.push unit
            liftST $ void $ STRef.write false r
            do
              eio.push unit
              eio.push unit
            res <- liftST $ STRef.read n
            shouldEqual res 3

          describe "derivative" do
            it "should give some sane approximation" $ liftEffect do
              { event, push } <- liftST $ Event.create
              rf <- liftEffect $ Ref.new []
              unsub <- Event.subscribe (UnoptimizedPoll.sample_ (UnoptimizedPoll.derivative' (UnoptimizedPoll.fixB 1.0 (map (add 1.0))) (UnoptimizedPoll.fixB 1.0 (map (mul 3.0)))) event) (\i -> Ref.modify_ (Array.cons i) rf)
              liftEffect do
                push unit
                push unit
                push unit
                push unit
                o <- Ref.read rf
                o `shouldEqual` [ 54.0, 18.0, 6.0, 0.0 ]
                unsub

          describe "UnoptimizedPoll.integral" do
            it "should give some sane approximation" $ liftEffect do
              { event, push } <- liftST $ Event.create
              rf <- liftEffect $ Ref.new []
              unsub <- Event.subscribe (UnoptimizedPoll.sample_ (UnoptimizedPoll.integral' 42.0 (UnoptimizedPoll.fixB 1.0 (map (add 1.0))) (UnoptimizedPoll.fixB 1.0 (map (mul 3.0)))) event) (\i -> Ref.modify_ (Array.cons i) rf)
              liftEffect do
                push unit
                push unit
                push unit
                push unit
                o <- Ref.read rf
                o `shouldEqual` [ 120.0, 66.0, 48.0, 42.0 ]
                unsub

        describe "Unique to Event" do
          -- this test shows how a UnoptimizedPoll.poll based framework could be used
          -- to emit html, where the webpage is a UnoptimizedPoll.poll and it is
          -- rendered based on an initial event
          it "should fire in order for UnoptimizedPoll.polls" $ liftEffect do
            r <- liftST $ STRef.new []
            ep <- liftST $ Event.create
            let
              -- this is going to be tricky
              -- before, we could emit and then do some more work
              -- now, however, emission is last
              -- we need to fix that
              bhv c = UnoptimizedPoll.poll \e0 -> makeEvent \s0 -> s0 e0 \f0 -> do
                -- first element
                justOne $ f0 "div"
                justNone do
                  void
                    $ s0
                        ( UnoptimizedPoll.sample
                            ( UnoptimizedPoll.poll \e1 ->
                                merge
                                  [ UnoptimizedPoll.sample (UnoptimizedPoll.poll \e2 -> makeEvent \s2 -> s2 e2 \f2 -> justOne (f2 "span")) e1
                                  , UnoptimizedPoll.sample c e1
                                  , UnoptimizedPoll.sample (UnoptimizedPoll.poll \e2 -> makeEvent \s2 -> s2 e2 \f2 -> justOne (f2 "b")) e1
                                  ]
                            )
                            e0
                        )
                    $ justOne
            u <- subscribe (UnoptimizedPoll.sample (bhv (bhv (bhv ((bhv $ UnoptimizedPoll.poll \e2 -> makeEvent \s2 -> s2 e2 \f2 -> justOne (f2 "h3")))))) ep.event) \i ->
              liftST $ void $ STRef.modify (flip Array.snoc i) r
            ep.push identity
            v <- liftST $ STRef.read r
            v `shouldEqual`
              [
                -- first level
                "div"
              , "span"
              ,
                -- second level
                "div"
              , "span"
              ,
                -- third level
                "div"
              , "span"
              ,
                -- fourth level
                "div"
              , "span"
              , "h3"
              , "b"
              ,
                -- third level
                "b"
              ,
                -- second level
                "b"
              ,
                -- first level
                "b"
              ]
            u
          it "should fire in order for UnoptimizedPoll.polls 2" $ liftEffect do
            r <- liftST $ STRef.new []
            ep <- liftST $ Event.create
            let
              bhv c = UnoptimizedPoll.poll \e0 -> makeEvent \s0 -> s0 e0 \f0 -> do
                -- first element
                justOne $ f0 "div"
                justNone $ void
                  $ s0
                      ( UnoptimizedPoll.sample
                          ( UnoptimizedPoll.poll \e1 ->
                              merge
                                [ UnoptimizedPoll.sample (UnoptimizedPoll.poll \e2 -> makeEvent \s2 -> s2 e2 \f2 -> justOne (f2 "span")) e1
                                , UnoptimizedPoll.sample c e1
                                , UnoptimizedPoll.sample (UnoptimizedPoll.poll \e2 -> makeEvent \s2 -> s2 e2 \f2 -> justOne (f2 "b")) e1
                                , UnoptimizedPoll.sample c e1
                                ]
                          )
                          e0
                      )
                  $ justOne
            u <- subscribe (UnoptimizedPoll.sample (bhv (bhv $ UnoptimizedPoll.poll \e2 -> makeEvent \s2 -> s2 e2 \f2 -> justOne (f2 "h3"))) ep.event) \i ->
              liftST $ void $ STRef.modify (flip Array.snoc i) r
            ep.push identity
            v <- liftST $ STRef.read r
            v `shouldEqual`
              [
                -- first level
                "div"
              , "span"
              ,
                -- second level
                "div"
              , "span"
              , "h3"
              , "b"
              , "h3"
              -- first level
              , "b"
              , -- second level
                "div"
              , "span"
              , "h3"
              , "b"
              , "h3"
              ]
            u
          it "should respond correctly to internal pushes" $ liftEffect do
            r <- liftST $ STRef.new []
            ep <- liftST $ Event.createPure
            let
              evt = makeEvent \s -> s ep.event \i -> do
                justOne i
                justNone do
                  when i (ep.push (not i))
            u <- subscribe evt \i ->
              liftST $ void $ STRef.modify (flip Array.snoc i) r
            liftST $ ep.push true
            v <- liftST $ STRef.read r
            v `shouldEqual`
              [ true
              , false
              ]
            u
          it "throttle throttles 1" do
            { event, push } <- liftST $ Event.create
            rf <- liftEffect $ Ref.new []
            unsub <- liftEffect $ Event.subscribe (throttle (Milliseconds 1000.0) event) (\i -> Ref.modify_ (Array.cons i) rf)
            liftEffect do
              under Op withTime push 1
              under Op withTime push 2
              under Op withTime push 3
              under Op withTime push 4
            delay (Milliseconds 1500.0)
            liftEffect do
              under Op withTime push 5
              under Op withTime push 6
              o <- Ref.read rf
              map _.value o `shouldEqual` [ 5, 1 ]
              unsub
          it "throttle throttles 2" do
            let
              f emitSecond = do
                { event, push } <- liftST $ Event.create
                rf <- liftEffect $ Ref.new []
                unsub <- liftEffect $ Event.subscribe (throttle (Milliseconds 500.0) event) (\i -> Ref.modify_ (Array.cons i) rf)
                liftEffect $ under Op withTime push unit
                when emitSecond do
                  liftEffect $ under Op withTime push unit
                delay $ Milliseconds 250.0
                liftEffect $ under Op withTime push unit
                delay $ Milliseconds 300.0
                liftEffect $ under Op withTime push unit
                liftEffect $ under Op withTime push unit
                o <- liftEffect $ Ref.read rf
                length o `shouldEqual` 2
                liftEffect $ unsub
            f true
            f false
          it "should not memoize" $ liftEffect do
            { push, event } <- liftST Event.create
            count <- Ref.new 0
            let
              fn v =
                unsafePerformEffect do
                  Ref.modify_ (add 1) count
                  pure $ v
            let mapped = identity (map fn event)
            u1 <- Event.subscribe mapped (pure (pure unit))
            u2 <- Event.subscribe mapped (pure (pure unit))
            push 0
            Ref.read count >>= shouldEqual 2
            u1
            u2
          it "should memoize" $ liftEffect do
            { push, event } <- liftST $ Event.create
            count <- liftST $ STRef.new 0
            let
              fn v =
                unsafePerformEffect do
                  void $ liftST $ STRef.modify (add 1) count
                  pure $ v
            mmz <- memoize (map fn event)
            u1 <- Event.subscribe mmz.event mempty
            u2 <- Event.subscribe mmz.event mempty
            push 0
            (liftST $ STRef.read count) >>= shouldEqual 1
            u1 *> u2 *> mmz.unsubscribe
          it "should mailbox" $ liftEffect do
            r <- liftST $ STRef.new []
            e <- liftST $ Event.mailbox
            u <- Event.subscribe (e.event 3 <|> e.event 4) \i ->
              liftST $ void $ STRef.modify (Array.cons i) r
            e.push { address: 42, payload: true }
            e.push { address: 43, payload: true }
            e.push { address: 44, payload: true }
            e.push { address: 3, payload: true } --
            e.push { address: 42, payload: false }
            e.push { address: 43, payload: true }
            e.push { address: 43, payload: false }
            e.push { address: 4, payload: false } --
            e.push { address: 42, payload: false }
            e.push { address: 43, payload: true }
            e.push { address: 3, payload: false } --
            e.push { address: 101, payload: true }
            o <- liftST $ STRef.read r
            o `shouldEqual` [ false, false, true ]
            u

          it "should mailboxS" $ liftEffect do
            r <- liftST $ STRef.new []
            e <- liftST $ Event.mailboxS
            u <- Event.subscribe (e.event "3" <|> e.event "4") \i ->
              liftST $ void $ STRef.modify (Array.cons i) r
            e.push { address: "42", payload: true }
            e.push { address: "43", payload: true }
            e.push { address: "44", payload: true }
            e.push { address: "3", payload: true } --
            e.push { address: "42", payload: false }
            e.push { address: "43", payload: true }
            e.push { address: "43", payload: false }
            e.push { address: "4", payload: false } --
            e.push { address: "42", payload: false }
            e.push { address: "43", payload: true }
            e.push { address: "3", payload: false } --
            e.push { address: "101", payload: true }
            o <- liftST $ STRef.read r
            o `shouldEqual` [ false, false, true ]
            u

          describe "Performance" do
            it "handles 10 subscriptions with a simple event and 1000 pushes" $ liftEffect do
              starts <- getTime <$> now
              r <- liftST $ STRef.new []
              { push, event } <- liftST $ Event.create
              us <- sequence $ replicate 10 $ subscribe (map (add 1) $ map (add 1) event) \i ->
                liftST $ void $ STRef.modify (Array.cons i) r
              for_ (replicate 1000 3) push
              sequence_ us
              ends <- getTime <$> now
              write ("Duration: " <> show (ends - starts) <> "\n")
            it "handles 1000 subscriptions with a simple event and 10 pushes" $ liftEffect do
              starts <- getTime <$> now
              r <- liftST $ STRef.new []
              { push, event } <- liftST $ Event.create
              us <- sequence $ replicate 1000 $ subscribe (map (add 1) $ map (add 1) event) \i ->
                liftST $ void $ STRef.modify (Array.cons i) r
              for_ (replicate 10 3) push
              sequence_ us
              ends <- getTime <$> now
              write ("Duration: " <> show (ends - starts) <> "\n")
            it "handles 1 subscription with a 10-nested event + 100 alts and 100 pushes" $ liftEffect do
              starts <- getTime <$> now
              r <- liftST $ STRef.new []
              { push, event } <- liftST $ Event.create
              let e = merge $ replicate 100 $ foldr ($) event (replicate 10 (map (add 1)))
              u <- subscribe e \i -> liftST $ void $ STRef.modify (Array.cons i) r
              for_ (replicate 100 3) push
              u
              ends <- getTime <$> now
              write ("Duration: " <> show (ends - starts) <> "\n")
            it "handles 1 subscription with a 10-nested event + array of 100 and 100 pushes" $ liftEffect do
              starts <- getTime <$> now
              r <- liftST $ STRef.new []
              { push, event } <- liftST $ Event.create
              let event' = map (replicate 100) $ foldr ($) event (replicate 10 (map (add 1)))
              u <- subscribe event' \i ->
                liftST $ void $ STRef.modify (Array.cons i) r
              for_ (replicate 100 3) push
              u
              ends <- getTime <$> now
              write ("Duration: " <> show (ends - starts) <> "\n")
