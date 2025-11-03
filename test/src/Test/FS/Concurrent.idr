module Test.FS.Concurrent

import Test.FS.Runner

%default total

parameters {auto sr : Sink (Action Nat)}
           {auto so : Sink Nat}
           {auto ti : TimerH e}

  timedNats : Nat -> Clock Duration -> AsyncStream e es Nat
  timedNats x cl = bracket (Runner.alloc x) cleanup $ \n => timed cl n.val

  errNats : Nat -> Clock Duration -> AsyncStream e [String] Nat
  errNats x cl =
    bracket (Runner.alloc x) cleanup $ \n =>
      take 4 (timed cl n.val) >> throw "Oops" >> timed cl n.val

  mergeSuccess : AsyncStream e [] Void
  mergeSuccess =
       merge [timedNats 1 10.ms, timedNats 2 21.ms, timedNats 3 33.ms]
    |> P.take 10
    |> toSink

  mergeErr : AsyncStream e [String] Void
  mergeErr =
       merge [errNats 1 10.ms, timedNats 2 21.ms, timedNats 3 33.ms]
    |> P.take 10
    |> toSink

  mergeHL : AsyncStream e [] Void
  mergeHL =
       mergeHaltL (P.take 3 $ timedNats 1 10.ms) (timedNats 2 21.ms)
    |> toSink

  mergeHLErr : AsyncStream e [String] Void
  mergeHLErr =
       mergeHaltL (errNats 1 10.ms) (timedNats 2 21.ms)
    |> toSink

  mergeHLErr2 : AsyncStream e [String] Void
  mergeHLErr2 =
       mergeHaltL (timedNats 2 21.ms) (errNats 1 10.ms)
    |> toSink

  mergeBoth : AsyncStream e [] Void
  mergeBoth =
       mergeHaltBoth (P.take 3 $ timedNats 1 10.ms) (timedNats 2 21.ms)
    |> toSink

  mergeBoth2 : AsyncStream e [] Void
  mergeBoth2 =
       mergeHaltBoth (timedNats 2 21.ms) (P.take 3 $ timedNats 1 10.ms)
    |> toSink

  mergeBothErr : AsyncStream e [String] Void
  mergeBothErr =
       mergeHaltBoth (errNats 1 10.ms) (timedNats 2 21.ms)
    |> toSink

  mergeBothErr2 : AsyncStream e [String] Void
  mergeBothErr2 =
       mergeHaltBoth (timedNats 2 21.ms) (errNats 1 10.ms)
    |> toSink

succRes : List (Event Nat Nat)
succRes =
     map Alloc [1,2,3]
  ++ [Out 1, Out 1, Out 2, Out 1, Out 3, Out 1, Out 2, Out 1, Out 1, Out 2]
  ++ map Release [3,2,1]

hlRes : List (Event Nat Nat)
hlRes = map Alloc [1,2] ++ [Out 1, Out 1, Out 2, Out 1] ++ map Release [1,2]

hlRes2 : List (Event Nat Nat)
hlRes2 = map Alloc [2,1] ++ [Out 1, Out 1, Out 2, Out 1] ++ map Release [1,2]

hlErrRes : List (Event Nat Nat)
hlErrRes =
  map Alloc [1,2] ++ [Out 1, Out 1, Out 2, Out 1, Out 1] ++ map Release [1,2]

hlErrRes2 : List (Event Nat Nat)
hlErrRes2 =
  map Alloc [2,1] ++ [Out 1, Out 1, Out 2, Out 1, Out 1] ++ map Release [1,2]

errRes : List (Event Nat Nat)
errRes =
     map Alloc [1,2,3]
  ++ [Out 1, Out 1, Out 2, Out 1, Out 3, Out 1]
  ++ map Release [1,2,3]

covering
instrs : TimerH e => List (FlatSpecInstr e)
instrs =
  [ "a merged stream" `should` "run to completion if all child streams succeed" `at`
      assert (testNN mergeSuccess) (succeed' succRes)
  , it `should` "fail with an error after the first child failed" `at`
      assert (testNN mergeErr) (failed "Oops" errRes)
  , "a stream merged vith mergeHaltL" `should` "stop when the first stream is exhausted" `at`
      assert (testNN mergeHL) (succeed' hlRes)
  , it `should` "stop, if the first stream fails with an error" `at`
      assert (testNN mergeHLErr) (failed "Oops" hlErrRes)
  , it `should` "stop, if the second stream fails with an error" `at`
      assert (testNN mergeHLErr2) (failed "Oops" hlErrRes2)
  , "a stream merged vith mergeHaltBoth" `should` "stop when the first stream is exhausted" `at`
      assert (testNN mergeBoth) (succeed' hlRes)
  , it `should` "stop when the second stream is exhaused" `at`
      assert (testNN mergeBoth2) (succeed' hlRes2)
  , it `should` "stop, if the first stream fails with an error" `at`
      assert (testNN mergeBothErr) (failed "Oops" hlErrRes)
  , it `should` "stop, if the second stream fails with an error" `at`
      assert (testNN mergeBothErr2) (failed "Oops" hlErrRes2)
  ]

export covering
specs : TimerH e => TestTree e
specs = flatSpec "Concurrent Spec" instrs
