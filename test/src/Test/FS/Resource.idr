module Test.FS.Resource

import Data.List
import public Test.FS.Runner

%default total

five : Nat
five = 5

parameters {auto sr : Sink (Action Nat)}

  acq : Nat -> AsyncStream e [] Nat
  acq x = do
    n <- acquire (Runner.alloc x) cleanup
    P.replicate n.val five

  acqErr : AsyncStream e [String] Nat
  acqErr = do
    n <- acquire (Runner.alloc Z) cleanup
    P.replicate 1 five
    P.replicate 1 five
    throw "Oops"
    P.replicate 3 five

  acqScoped : AsyncStream e [String] Nat
  acqScoped =
    newScope (weakenErrors $ acq 1) >> P.replicate 2 five

covering
instrs : List (FlatSpecInstr e)
instrs =
  [ "a stream's resource" `should` "be acquired before the stream is run" !:
      assertAcquired Nat (acq 200) [200]

  , it `should` "be released after the stream is exhausted" !:
      assertReleased Nat (acq 200) [200]

  , it `should` "be released after the last value has been emitted" !:
      assertEvents Nat (acq 2) [Alloc 2,Out 5,Out 5,Release 2]

  , it `should` "be released after the stream fails with an error" !:
      assertEvents Nat acqErr [Alloc 0,Out 5,Out 5,Release 0]

  , it `should` "be released when its scope closes" !:
      assertEvents Nat acqScoped [Alloc 1,Out 5,Release 1,Out 5,Out 5]

  , it `should` "not be acquired if the stream is exhausted early" !:
      assertAcquired Nat (P.take 2 $ acq 10 >> acq 20) [10]

  , it `should` "be released if the stream is exhausted early" !:
      assertReleased Nat (P.take 2 $ acq 10 >> acq 20) [10]

  , it `should` "be released after emitting output if the stream is exhausted early" !:
      assertEvents Nat (P.take 2 $ acq 10 >> acq 20)
        [Alloc 10, Out 5, Out 5, Release 10]

  , it `should` "be acquired and released in the correct order when concatenating streams" !:
      assertEvents Nat (P.take 3 $ acq 2 >> acq 20)
        [Alloc 2, Out 5, Out 5, Alloc 20, Out 5, Release 20, Release 2]

  , "a stream's resources" `should` "be acquired in the correct order" !:
      assertAcquired Nat (acq 10 >> acq 20) [10,20]

  , they `should` "be released in reverse order of acquisition" !:
      assertReleased Nat (acq 10 >> acq 20) [20,10]
  ]

export covering
specs : TestTree e
specs = flatSpec "Resource Spec" instrs
