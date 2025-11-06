module Test.FS.Bracket

import public Test.FS.Runner

%default total

five : Nat
five = 5

parameters {auto sr : Sink (Action Nat)}

  acq : AsyncStream e [] Nat
  acq = do
    bracket (allocNat 0) cleanup $ \_ => do
      bracket (allocNat 1) cleanup $ \_ => do
        P.replicate 2 five
        bracket (allocNat 2) cleanup $ \_ => do
          flatMap (P.replicate 1 five) $ \v => do
            bracket (allocNat 3) cleanup $ \_ => emit v
      bracket (allocNat 4) cleanup $ \_ => do
        P.replicate 4 five

covering
instrs : List (FlatSpecInstr e)
instrs =
  [ "bracketed resources" `should` "be acquired from outer to inner" !:
      assertAcquired Nat acq [0,1,2,3,4]
  , they `should` "be released in reverse order" !:
      assertReleased Nat acq [3,2,1,4,0]
  , they `should` "be released after values in scope have been emitted" !:
      assertEvents Nat acq
        [ Alloc 0
        , Alloc 1, Out 5, Out 5
        , Alloc 2
        , Alloc 3, Out 5
        , Release 3
        , Release 2
        , Release 1
        , Alloc 4, Out 5, Out 5, Out 5, Out 5, Release 4
        , Release 0
        ]
  ]

export covering
specs : TestTree e
specs = flatSpec "Bracket Spec" instrs
