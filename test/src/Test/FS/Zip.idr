module Test.FS.Zip

import public Test.FS.Runner

%default total

parameters {auto sr : Sink (Action Nat)}
  inner : Nat -> AsyncStream e [] Nat
  inner n =
    bracket (allocNat n) cleanup $ \x => P.replicate x.val x.val

  s1 : AsyncStream e [] Nat
  s1 =
    bracket (allocNat 0) cleanup $ \_ =>
      P.iterate (S Z) S |> P.take 5 |> bind inner

  s2 : AsyncStream e [] Nat
  s2 =
    bracket (allocNat 10) cleanup $ \_ =>
      P.iterate (S 10) S |> P.take 6 |> bind inner

covering
instrs : List (FlatSpecInstr e)
instrs =
  [ "streams zipped with zipWith" `should` "abort once the first stream is exhausted" !:
      assertOut Nat (P.zipWith s1 s2 (+))
        [12,13,13,14,14,14,15,15,15,15,16,17,17,17,17]
  , they `should` "allocate resources in the correct order" !:
      assertAcquired Nat (P.zipWith s1 s2 (+)) [0,1,10,11,2,3,4,5,12]
  , they `should` "release resources in the correct order" !:
      assertReleased Nat (P.zipWith s1 s2 (+)) [1,2,3,4,11,5,0,12,10]
  , they `should` "produce events in the correct order" !:
      assertEvents Nat (P.zipWith s1 s2 (+))
        [ Alloc 0
        , Alloc 1
        , Alloc 10
        , Alloc 11
        , Out 12
        , Release 1
        , Alloc 2
        , Out 13
        , Out 13
        , Release 2
        , Alloc 3
        , Out 14
        , Out 14
        , Out 14
        , Release 3
        , Alloc 4
        , Out 15
        , Out 15
        , Out 15
        , Out 15
        , Release 4
        , Alloc 5
        , Out 16
        , Release 11
        , Alloc 12
        , Out 17
        , Out 17
        , Out 17
        , Out 17
        , Release 5
        , Release 0
        , Release 12
        , Release 10
        ]

  ]

export covering
specs : TestTree e
specs = flatSpec "Zip Spec" instrs
