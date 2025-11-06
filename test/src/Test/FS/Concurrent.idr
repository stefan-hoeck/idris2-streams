module Test.FS.Concurrent

import Test.FS.Runner

%default total

parameters {auto sr : Sink (Action Nat)}
           {auto ti : TimerH e}

  timedN : Nat -> Clock Duration -> AsyncStream e es Nat
  timedN x cl =
    bracket (Runner.alloc x) cleanup $ \n => do
      sc <- scope
      exec $ logScope "timedN" sc
      timed cl n.val

  errN : Nat -> Clock Duration -> AsyncStream e [String] Nat
  errN x cl =
    bracket (Runner.alloc x) cleanup $ \n =>
      P.take 5 (timed cl n.val) >> throw "Oops" >> timed cl n.val

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

  parallel : AsyncStream e [String] (AsyncStream e [String] Nat)
  parallel =
    bracket (Runner.alloc Z) cleanup $ \n => do
      sc <- scope
      exec $ logScope "parallel" sc
      timed 10.ms n.val |> P.runningCount |> P.take 3 |> mapOutput (\n => timedN n 3.ms |> P.take 5)

  switchOuter : AsyncStream e [String] Nat
  switchOuter = timedN 0 10.ms |> P.count |> P.take 3

  switchInner : Nat -> AsyncStream e [String] Nat
  switchInner n = timedN n 3.ms |> P.take 5

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

  -- , "a stream created with switchMap" `should` "stop inner streams upon output from the outer stream" !:
  --     assertOut Nat (switchMap switchInner switchOuter) [1,1,1,2,2,2,3,3,3,3,3]
  ]

export covering
specs : TimerH e => TestTree e
specs = flatSpec "Concurrent Spec" instrs
