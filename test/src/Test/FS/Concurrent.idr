module Test.FS.Concurrent

import Test.FS.Runner

%default total

parameters {auto sr : Sink (Action Nat)}
           {auto so : Sink Nat}
           {auto ti : TimerH e}

  timedNats : Nat -> Clock Duration -> AsyncStream e es Nat
  timedNats x cl = do
    n <- acquire (Runner.alloc x) cleanup
    timed cl n.val

  errNats : Nat -> Clock Duration -> AsyncStream e [String] Nat
  errNats x cl = do
    n <- acquire (Runner.alloc x) cleanup
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

succRes : List (Event Nat Nat)
succRes =
     map Alloc [1,2,3]
  ++ [Out 1, Out 1, Out 2, Out 1, Out 3, Out 1, Out 2, Out 1, Out 1, Out 2]
  ++ map Release [3,2,1]

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
  ]

export covering
specs : TimerH e => TestTree e
specs = flatSpec "Concurrent Spec" instrs
