module Test.Main where

import Prelude

import Control.Alt ((<|>))
import Control.Plus (empty)
import Data.Array (cons, replicate)
import Data.Filterable (filter)
import Data.JSDate (getTime, now)
import Data.Traversable (foldr, for_, oneOf, sequence)
import Data.Tuple (Tuple(..))
import Data.Tuple.Nested ((/\))
import Effect (Effect)
import Effect.Aff (launchAff_)
import Effect.Class (liftEffect)
import Effect.Ref as Ref
import Effect.Unsafe (unsafePerformEffect)
import FRP.Event (sampleOn)
import FRP.Event as Event
import FRP.Event.Class (class IsEvent, bang, fold)
import FRP.Event.Legacy as Legacy
import FRP.Event.Memoizable as Memoizable
import FRP.Event.Memoize (memoize, memoizeIfMemoizable)
import FRP.Event.Memoized as Memoized
import FRP.Event.STMemoized as STMemoized
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Test.Spec.Console (write)
import Test.Spec.Reporter (consoleReporter)
import Test.Spec.Runner (runSpec)

main :: Effect Unit
main = do
  launchAff_
    $ runSpec [ consoleReporter ] do
        let
          suite
            :: forall event
             . IsEvent event
            => String
            -> (forall i o. event i -> (forall event'. IsEvent event' => event' i -> event' o) -> event o)
            -> (forall a. Effect { push :: a -> Effect Unit, event :: event a })
            -> (forall a. event a -> (a -> Effect Unit) -> Effect (Effect Unit))
            -> Spec Unit
          suite name context create subscribe =
            describe ("Testing " <> name) do
              it "should do simple stuff" do
                liftEffect do
                  rf <- Ref.new []
                  unsub <- subscribe (context (bang 0) identity) \i -> Ref.modify_ (cons i) rf
                  o <- Ref.read rf
                  o `shouldEqual` [ 0 ]
                  unsub
              it "should do complex stuff" do
                liftEffect do
                  rf <- Ref.new []
                  { push, event } <- create
                  unsub1 <- subscribe (context event identity) \i -> Ref.modify_ (cons i) rf
                  push 0
                  o <- Ref.read rf
                  o `shouldEqual` [ 0 ]
                  unsub2 <- subscribe (context event identity) \i -> Ref.modify_ (cons (negate i)) rf
                  o' <- Ref.read rf
                  o' `shouldEqual` [ 0 ]
                  push 1
                  o'' <- Ref.read rf
                  o'' `shouldEqual` [ -1, 1, 0 ]
                  unsub1 *> unsub2
              it "should do a lot more complex addition" do
                liftEffect do
                  rf <- Ref.new []
                  let
                    x = context (bang 0) \i ->
                      let
                        add1 = map (add 1) i
                        add2 = map (add 2) add1
                        add3 = map (add 3) add2
                        add4 = map (add 4) add3
                      in
                        add1 <|> add4
                  unsub <- subscribe x \i -> Ref.modify_ (cons i) rf
                  o <- Ref.read rf
                  o `shouldEqual` [ 10, 1 ]
                  unsub
              it "should handle alt" do
                liftEffect do
                  rf <- Ref.new []
                  let
                    x = context (bang 0) \i ->
                      let
                        add1 = (map (add 1) i)
                        add2 = map (add 2) add1
                        add3 = map (add 3) add2
                        add4 = map (add 4) add3
                        altr = add1 <|> add2 <|> empty <|> add4 <|> empty
                      in
                        add1 <|> altr
                  unsub <- subscribe x \i -> Ref.modify_ (cons i) rf
                  o <- Ref.read rf
                  o `shouldEqual` [ 10, 3, 1, 1 ]
                  unsub
              it "should handle filter 1" do
                liftEffect do
                  rf <- Ref.new []
                  let
                    x = context (bang 0) \i ->
                      let
                        add1 = map (add 1) i
                        add2 = map (add 2) add1
                        add3 = map (add 3) add2
                        add4 = map (add 4) add3
                        altr = add1 <|> add2 <|> empty <|> add4 <|> empty
                        fm = (filter (_ < 5) altr)
                      in
                        add1 <|> fm
                  unsub <- subscribe x (\i -> Ref.modify_ (cons i) rf)
                  o <- Ref.read rf
                  o `shouldEqual` [ 3, 1, 1 ]
                  unsub
              it "should handle filter 2" do
                liftEffect do
                  rf <- Ref.new []
                  let add1 = (map (add 1) (bang 0))
                  let add2 = map (add 2) add1
                  let add3 = map (add 3) add2
                  let add4 = map (add 4) add3
                  let altr = add1 <|> add2 <|> empty <|> add4 <|> empty
                  let fm = (filter (_ > 5) altr)
                  unsub <- subscribe (add1 <|> fm) (\i -> Ref.modify_ (cons i) rf)
                  o <- Ref.read rf
                  o `shouldEqual` [ 10, 1 ]
                  unsub
              it "should handle fold 0" do
                liftEffect do
                  rf <- Ref.new []
                  { push, event } <- create
                  let
                    x = context event \i -> do
                      let foldy = (fold (\_ b -> b + 1) i 0)
                      let add2 = map (add 2) foldy
                      let add3 = map (add 3) add2
                      let add4 = map (add 4) add3
                      let altr = foldy <|> add2 <|> empty <|> add4 <|> empty
                      let fm = (filter (_ > 5) altr)
                      foldy <|> fm
                  unsub <- subscribe x (\i -> Ref.modify_ (cons i) rf)
                  push unit
                  Ref.read rf >>= shouldEqual [ 10, 1 ]
                  Ref.write [] rf
                  push unit
                  Ref.read rf >>= shouldEqual [ 11, 2 ]
                  Ref.write [] rf
                  push unit
                  Ref.read rf >>= shouldEqual [ 12, 3 ]
                  unsub
              it "should handle fold 1" do
                liftEffect do
                  rf <- Ref.new []
                  { push, event } <- create
                  let
                    x = context event \i -> do
                      let add1 = map (add 1) i
                      let add2 = map (add 2) add1
                      let add3 = map (add 3) add2
                      let foldy = fold (\a b -> a + b) add3 0
                      let add4 = map (add 4) add3
                      let altr = foldy <|> add2 <|> empty <|> add4 <|> empty
                      sampleOn add2 (map (\a b -> b /\ a) (filter (_ > 5) altr))
                  unsub <- subscribe x (\i -> Ref.modify_ (cons i) rf)
                  push 0
                  Ref.read rf >>= shouldEqual [ Tuple 3 10, Tuple 3 6 ]
                  Ref.write [] rf
                  push 0
                  Ref.read rf >>= shouldEqual [ Tuple 3 10, Tuple 3 12 ]
                  Ref.write [] rf
                  push 0
                  Ref.read rf >>= shouldEqual [ Tuple 3 10, Tuple 3 18 ]
                  unsub
        suite "Event" (\i f -> f i) Event.create Event.subscribe
        suite "Legacy" (\i f -> f i) Legacy.create Legacy.subscribe
        suite "Memoized" (\i f -> f i) Memoized.create Memoized.subscribe
        suite "Memoizable" (\i f -> f i) Memoizable.create Memoizable.subscribe
        suite "STMemoizable"
          ( \i io -> STMemoized.run' (Memoizable.toEvent i)
              (map (Memoizable.fromEvent <<< STMemoized.toEvent) io)
              (map Memoizable.fromEvent io)
          )
          Memoizable.create
          Memoizable.subscribe
        let
          performanceSuite
            :: forall event
             . IsEvent event
            => String
            -> (forall i o. event i -> (event i -> event o) -> event o)
            -> (forall a. Effect { push :: a -> Effect Unit, event :: event a })
            -> (forall a. event a -> (a -> Effect Unit) -> Effect (Effect Unit))
            -> (forall a. Array (event a) -> event a)
            -> Spec Unit
          performanceSuite name context create subscribe merger =
            describe ("Performance testing " <> name) do
              it "handles 10 subscriptions with a simple event and 1000 pushes" do
                liftEffect do
                  starts <- getTime <$> now
                  rf <- Ref.new []
                  { push, event } <- create
                  unsubs <- sequence $ replicate 10 (subscribe (context event (\i -> map (add 1) $ map (add 1) i)) \i -> Ref.modify_ (cons i) rf)
                  for_ (replicate 1000 3) \i -> push i
                  for_ unsubs \unsub -> unsub
                  ends <- getTime <$> now
                  write ("Duration: " <> show (ends - starts) <> "\n")
              it "handles 1000 subscriptions with a simple event and 10 pushes" do
                liftEffect do
                  starts <- getTime <$> now
                  rf <- Ref.new []
                  { push, event } <- create
                  unsubs <- sequence $ replicate 1000 (subscribe (context event (\i -> map (add 1) $ map (add 1) i)) \i -> Ref.modify_ (cons i) rf)
                  for_ (replicate 10 3) \i -> push i
                  for_ unsubs \unsub -> unsub
                  ends <- getTime <$> now
                  write ("Duration: " <> show (ends - starts) <> "\n")
              it "handles 10 subscriptions with a 100-nested event and 100 pushes" do
                liftEffect do
                  starts <- getTime <$> now
                  rf <- Ref.new []
                  { push, event } <- create
                  let e = context event (\i -> foldr ($) i (replicate 100 (map (add 1))))
                  unsubs <- sequence $ replicate 10 (subscribe  e \i -> Ref.modify_ (cons i) rf)
                  for_ (replicate 100 3) \i -> push i
                  for_ unsubs \unsub -> unsub
                  ends <- getTime <$> now
                  write ("Duration: " <> show (ends - starts))
              it "handles 1 subscription with a 10-nested event + 100 alts and 100 pushes" do
                liftEffect do
                  starts <- getTime <$> now
                  rf <- Ref.new []
                  { push, event } <- create
                  let e = context event (\i -> merger $ replicate 100 $ foldr ($) i (replicate 10 (map (add 1))))
                  unsub <- subscribe e \i -> Ref.modify_ (cons i) rf
                  for_ (replicate 100 3) \i -> push i
                  unsub
                  ends <- getTime <$> now
                  write ("Duration: " <> show (ends - starts) <> "\n")
        performanceSuite "Event" (\i f -> f i) Event.create Event.subscribe oneOf
        performanceSuite "Legacy" (\i f -> f i) Legacy.create Legacy.subscribe oneOf
        performanceSuite "Memoized" (\i f -> f i) Memoized.create Memoized.subscribe oneOf
        performanceSuite "Memoizable" (\i f -> f i) Memoizable.create Memoizable.subscribe oneOf
        describe "Testing memoization" do
          it "should not memoize" do
            liftEffect do
              { push, event } <- Event.create
              count <- Ref.new 0
              let
                fn v =
                  unsafePerformEffect do
                    Ref.modify_ (add 1) count
                    pure $ v
              let mapped = identity (map fn event)
              unsub1 <- Event.subscribe mapped (pure (pure unit))
              unsub2 <- Event.subscribe mapped (pure (pure unit))
              push 0
              Ref.read count >>= shouldEqual 2
              unsub1
              unsub2

          it "should memoize" do
            liftEffect do
              { push, event } <- Event.create
              count <- Ref.new 0
              let
                fn v =
                  unsafePerformEffect do
                    Ref.modify_ (add 1) count
                    pure $ v
              mapped <- memoize (map fn event)
              unsub1 <- Event.subscribe mapped (pure (pure unit))
              unsub2 <- Event.subscribe mapped (pure (pure unit))
              push 0
              Ref.read count >>= shouldEqual 1
              unsub1
              unsub2
          it "should memoize when using Memoized.Event" do
            liftEffect do
              { push, event } <- Memoized.create
              count <- Ref.new 0
              let
                fn v =
                  unsafePerformEffect do
                    Ref.modify_ (add 1) count
                    pure $ v
              let mapped = identity (map fn event)
              unsub1 <- Memoized.subscribe mapped (pure (pure unit))
              unsub2 <- Memoized.subscribe mapped (pure (pure unit))
              push 0
              Ref.read count >>= shouldEqual 1
              unsub1
              unsub2
          it "should memoize when using Memoizable.Event if we ask for it explicitly" do
            liftEffect do
              { push, event } <- Memoizable.create
              count <- Ref.new 0
              let
                fn v =
                  unsafePerformEffect do
                    Ref.modify_ (add 1) count
                    pure $ v
              let mapped = identity (memoizeIfMemoizable (map fn (map identity (map identity (map identity event)))))
              unsub1 <- Memoizable.subscribe mapped (pure (pure unit))
              unsub2 <- Memoizable.subscribe mapped (pure (pure unit))
              push 0
              Ref.read count >>= shouldEqual 1
              unsub1
              unsub2
          it "should _not_ memoize when using Memoizable.Event if we _don't_ ask for it explicitly" do
            liftEffect do
              { push, event } <- Memoizable.create
              count <- Ref.new 0
              let
                fn v =
                  unsafePerformEffect do
                    Ref.modify_ (add 1) count
                    pure $ v
              let mapped = identity (map fn (map identity (map identity (map identity event))))
              unsub1 <- Memoizable.subscribe mapped (pure (pure unit))
              unsub2 <- Memoizable.subscribe mapped (pure (pure unit))
              push 0
              Ref.read count >>= shouldEqual 2
              unsub1
              unsub2
        describe "Legacy" do
          it "has a somewhat puzzling result when it adds itself to itself (2 + 2 = 3)" $ liftEffect do
            rf <- Ref.new []
            { push, event } <- Legacy.create
            unsub <- Legacy.subscribe (let x = event in (map add x) <*> x) \i -> Ref.modify_ (cons i) rf
            push 2
            push 1
            o <- Ref.read rf
            o `shouldEqual` [ 2, 3, 4 ]
