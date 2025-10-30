module Test.FS.Resource

import public Test.FS.Runner

%default total

five : Nat
five = 5

parameters {auto sr : Sink (Action Nat)}
           {auto so : Sink Nat}

  natStream : Nat -> AsyncStream e [] Void
  natStream x = do
    n <- acquire (Runner.alloc x) cleanup
    P.replicate n.val five |> toSink

  takeStream : Nat -> AsyncStream e [] Void
  takeStream x = do
    n <- acquire (Runner.alloc x) cleanup
    C.iterate (List Nat) Z S |> C.take n.val |> sinkAll

takeRes : Nat -> List (Event Nat Nat)
takeRes 0       = [Alloc 0, Release 0]
takeRes n@(S k) = [Alloc n] ++ map Out [0..k] ++ [Release n]

natRes : Nat -> List (Event Nat Nat)
natRes 0       = [Alloc 0, Release 0]
natRes n@(S k) = [Alloc n] ++ map (const $ Out 5) [0..k] ++ [Release n]

covering
instrs : List (FlatSpecInstr e)
instrs =
  [ "a stream's resource" `should` "be released after the stream is exhausted" `at`
      assert (testNN $ natStream 10000) (succeed' $ natRes 10000)
  , it `should` "be released after taking a predefined prefix of the stream" `at`
      assert (testNN $ takeStream 10000) (succeed' $ takeRes 10000)
  , it `should` "be released after processing an appended stream in the same scope" `at`
      assert (testNN $ takeStream 3 <+> natStream 2)
        (succeed' [Alloc 3, Out 0, Out 1, Out 2, Alloc 2, Out 5, Out 5, Release 2, Release 3])
  , it `should` "be released before processing an appended stream when wrapped in a new scope" `at`
      assert (testNN $ newScope (takeStream 10000) <+> natStream 20000)
        (succeed' $ takeRes 10000 ++ natRes 20000)
  , it `should` "be timely released when the stream is created within flatMap in a new scope" `at`
      assert (testNN $ emits [1..1000] |> bind (newScope . takeStream))
        (succeed' $ [1..1000] >>= takeRes)
  ]

export covering
specs : TestTree e
specs = flatSpec "Resource Spec" instrs
