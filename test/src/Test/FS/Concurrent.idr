module Test.FS.Concurrent

import FS.Concurrent.Signal
import Test.FS.Runner

%default total

parameters {auto sr : Sink (Action Nat)}
           {auto ti : TimerH e}

  timedN : Nat -> Clock Duration -> AsyncStream e es Nat
  timedN x cl = bracket (Runner.alloc x) cleanup $ \n => timed cl n.val

  timedNats : Nat -> Clock Duration -> AsyncStream e es Nat
  timedNats x cl =
    bracket (Runner.alloc x) cleanup $ \n => every cl (P.iterate (S Z) S)

  heldNats : AsyncStream e [] Nat
  heldNats =
    timedNats 0 5.ms |> signalOn 0 (timed 3.ms ()) |> P.take 5

  heldNats1 : AsyncStream e [] Nat
  heldNats1 = timedNats 0 5.ms |> signalOn1 (timed 8.ms ()) |> P.take 4

  heldNatsCont : AsyncStream e [] Nat
  heldNatsCont =
    timedNats 0 5.ms |> take 1 |> signalOn 0 (timed 3.ms ()) |> P.take 10

  errN : Nat -> Clock Duration -> AsyncStream e [String] Nat
  errN x cl =
    bracket (Runner.alloc x) cleanup $ \n =>
      P.take 5 (timed cl n.val) >> throw "Oops" >> timed cl n.val

  heldNatsErr : AsyncStream e [String] Nat
  heldNatsErr = errN 0 5.ms |> signalOn 0 (timed 3.ms ())

  mergeSucc : AsyncStream e [] Nat
  mergeSucc = merge [timedN 1 10.ms, timedN 2 20.ms, timedN 3 30.ms]

  mergeErr : AsyncStream e [String] Nat
  mergeErr = merge [errN 1 10.ms, timedN 2 21.ms, timedN 3 33.ms]

  mergeHL : AsyncStream e [] Nat
  mergeHL = mergeHaltL (P.take 3 $ timedN 1 10.ms) (timedN 2 20.ms)

  mergeHLErr : AsyncStream e [String] Nat
  mergeHLErr = mergeHaltL (errN 1 10.ms) (timedN 2 20.ms)

  mergeHLErr2 : AsyncStream e [String] Nat
  mergeHLErr2 = mergeHaltL (timedN 2 20.ms) (errN 1 10.ms)

  mergeBoth : AsyncStream e [] Nat
  mergeBoth = mergeHaltBoth (P.take 3 $ timedN 1 10.ms) (timedN 2 21.ms)

  mergeBoth2 : AsyncStream e [] Nat
  mergeBoth2 = mergeHaltBoth (timedN 2 21.ms) (P.take 3 $ timedN 1 10.ms)

  mergeBothErr : AsyncStream e [String] Nat
  mergeBothErr = mergeHaltBoth (errN 1 10.ms) (timedN 2 21.ms)

  mergeBothErr2 : AsyncStream e [String] Nat
  mergeBothErr2 = mergeHaltBoth (timedN 2 21.ms) (errN 1 10.ms)

  parallel_ :
       AsyncStream e [String] ()
    -> (Nat -> AsyncStream e [String] Nat)
    -> AsyncStream e [String] (AsyncStream e [String] Nat)
  parallel_ outer f =
    bracket (Runner.alloc Z) cleanup $ \n => do
      outer |> P.runningCount |> mapOutput f --

  parallel : AsyncStream e [String] (AsyncStream e [String] Nat)
  parallel =
    parallel_ (P.take 3 $ timed 10.ms ()) (\n => timedN n 3.ms |> P.take 5)

  parallelErr : AsyncStream e [String] (AsyncStream e [String] Nat)
  parallelErr =
    parallel_ (P.take 3 (timed 10.ms ()) >> throw "Oops") (\n => timedN n 3.ms)

  parallelInnerErr : AsyncStream e [String] (AsyncStream e [String] Nat)
  parallelInnerErr =
    parallel_ (timed 10.ms ()) $ \case
      5 => throw "Oops"
      n => timedN n 3.ms

  switchOuter : AsyncStream e [String] Nat
  switchOuter = timedN 0 10.ms |> P.runningCount |> P.take 3

  switchOuterErr : AsyncStream e [String] Nat
  switchOuterErr = P.take 2 switchOuter >> throw "Oops"

  switchInner : Nat -> AsyncStream e [String] Nat
  switchInner 3 = timedN 3 3.ms |> P.take 5
  switchInner n = timedN n 3.ms

  switchInnerLR : Nat -> AsyncStream e [String] Nat
  switchInnerLR 2 = exec (event Nat) >>= events
  switchInnerLR n = switchInner n

  switchInnerErr : Nat -> AsyncStream e [String] Nat
  switchInnerErr 2 = throw "Oops"
  switchInnerErr n = switchInner n

covering
instrs : TimerH e => List (FlatSpecInstr e)
instrs =
  [ "a merged stream" `should` "run to completion if all child streams succeed" !:
      assertSorted Nat (P.take 11 mergeSucc) [1,1,1,1,1,1,2,2,2,3,3]

  , it `should` "acquire all necessary resources" !:
      assertSortedAcquired Nat (P.take 11 mergeSucc) [1,2,3]

  , it `should` "release all acquired resources" !:
      assertSortedReleased Nat (P.take 11 mergeSucc) [1,2,3]

  , it `should` "fail with an error after the first child failed" !:
      assertErr Nat mergeErr "Oops"

  , it `should` "release all acquired resources after the first child failed" !:
      assertSortedReleased Nat mergeErr [1,2,3]

  , "a stream merged vith mergeHaltL" `should` "stop when the the first stream is exhausted" !:
      assertSorted Nat mergeHL [1,1,1,2]

  , it `should` "stop, if the first stream fails with an error" !:
      assertSorted Nat mergeHLErr [1,1,1,1,1,2,2]

  , it `should` "stop, if the second stream fails with an error" !:
      assertSorted Nat mergeHLErr2 [1,1,1,1,1,2,2]

  , it `should` "fail with an error after the first stream failed with an error" !:
      assertErr Nat mergeHLErr "Oops"

  , it `should` "fail with an error after the second stream failed with an error" !:
      assertErr Nat mergeHLErr2 "Oops"

  , it `should` "acquire all necessary resources" !:
      assertSortedAcquired Nat mergeHL [1,2]

  , it `should` "release all acquired resources" !:
      assertSortedReleased Nat mergeHL [1,2]

  , it `should` "release all acquired resources even if the first stream failed" !:
      assertSortedReleased Nat mergeHLErr [1,2]

  , it `should` "release all acquired resources even if the second stream failed" !:
      assertSortedReleased Nat mergeHLErr2 [1,2]

  , "a stream merged vith mergeHaltBoth" `should` "stop when the the first stream is exhausted" !:
      assertSorted Nat mergeBoth [1,1,1,2]

  , it `should` "stop when the the second stream is exhausted" !:
      assertSorted Nat mergeBoth2 [1,1,1,2]

  , it `should` "stop, if the first stream fails with an error" !:
      assertSorted Nat mergeBothErr [1,1,1,1,1,2,2]

  , it `should` "stop, if the second stream fails with an error" !:
      assertSorted Nat mergeBothErr2 [1,1,1,1,1,2,2]

  , it `should` "fail with an error after the first stream failed with an error" !:
      assertErr Nat mergeBothErr "Oops"

  , it `should` "fail with an error after the second stream failed with an error" !:
      assertErr Nat mergeBothErr2 "Oops"

  , it `should` "acquire all necessary resources" !:
      assertSortedAcquired Nat mergeBoth [1,2]

  , it `should` "release all acquired resources" !:
      assertSortedReleased Nat mergeBoth [1,2]

  , it `should` "release all acquired resources even if the first stream failed" !:
      assertSortedReleased Nat mergeBothErr [1,2]

  , it `should` "release all acquired resources even if the second stream failed" !:
      assertSortedReleased Nat mergeBothErr2 [1,2]

  , "a stream created with parJoin" `should` "run all inner streams to completion" !:
      assertSorted Nat (parJoin 3 parallel) [1,1,1,1,1,2,2,2,2,2,3,3,3,3,3]

  , it `should` "allocate all required resources" !:
      assertSortedAcquired Nat (parJoin 3 parallel) [0,1,2,3]

  , it `should` "release all acquired resources" !:
      assertSortedReleased Nat (parJoin 3 parallel) [0,1,2,3]

  , it `should` "release resources from inner streams before the ones from the outer stream" !:
      assertLastReleased Nat (parJoin 3 parallel) (Just 0)

  , it `should` "fail with an error once the outer stream fails" !:
      assertErr Nat (parJoin 3 parallelErr) "Oops"

  , it `should` "cleanup all allocated resources after the outer stream failed" !:
      assertReleasedAll Nat (parJoin 3 parallelErr)

  , it `should` "fail with an error once an inner stream fails" !:
      assertErr Nat (parJoin 10 parallelInnerErr) "Oops"

  , it `should` "cleanup all allocated resources after an inner stream failed" !:
      assertReleasedAll Nat (parJoin 10 parallelInnerErr)

  , "a stream created with switchMap" `should` "stop inner streams upon output from the outer stream" !:
      assertOut Nat (switchMap switchInner switchOuter) [1,1,1,2,2,3,3,3,3,3]

  , it `should` "abort long running effects from an inner stream upon output from the outer stream" !:
      assertOut Nat (switchMap switchInnerLR switchOuter) [1,1,1,3,3,3,3,3]

  , it `should` "allocate all required resources" !:
      assertSortedAcquired Nat (switchMap switchInner switchOuter) [0,1,2,3]

  , it `should` "release all allocated resources" !:
      assertSortedReleased Nat (switchMap switchInner switchOuter) [0,1,2,3]

  , it `should` "release resources from inner streams before the ones from the outer stream" !:
      assertLastReleased Nat (switchMap switchInner switchOuter) (Just 0)

  , it `should` "fail with an error once the outer stream fails" !:
      assertErr Nat (switchMap switchInner switchOuterErr) "Oops"

  , it `should` "cleanup all allocated resources after the outer stream failed" !:
      assertReleasedAll Nat (switchMap switchInner switchOuterErr)

  , it `should` "fail with an error once an inner stream fails" !:
      assertErr Nat (switchMap switchInnerErr switchOuter) "Oops"

  , it `should` "cleanup all allocated resources after an inner stream failed" !:
      assertReleasedAll Nat (switchMap switchInnerErr switchOuter)

  , "a stream created with hold" `should` "continuously emit the last value from the original stream" !:
      assertOut Nat heldNats [0,1,1,2,2]

  , it `should` "allocate all required resources" !:
      assertAcquired Nat heldNats [0]

  , it `should` "release all allocated resources" !:
      assertReleased Nat heldNats [0]

  , it `should` "fail with  an error if the inner stream fails" !:
      assertErr Nat heldNatsErr "Oops"

  , it `should` "release all allocated resources after failing with an error" !:
      assertReleased Nat heldNatsErr [0]

  , it `should` "continue emitting events after the inner stream is exhausted" !:
      assertOut Nat heldNatsCont [0,1,1,1,1,1,1,1,1,1]

  , it `should` "release resources after the inner stream is exhausted" !:
      assertEvents Nat heldNatsCont [Alloc 0, Out 0, Release 0, Out 1,Out 1,Out 1,Out 1,Out 1,Out 1,Out 1,Out 1,Out 1]

  , "a stream created with hold1" `should` "continuously emit the last value from the original stream" !:
      assertOut Nat heldNats1 [1,3,4,6]
  ]

export covering
specs : TimerH e => TestTree e
specs = flatSpec "Concurrent Spec" instrs
