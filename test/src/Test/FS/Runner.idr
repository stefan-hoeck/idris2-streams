module Test.FS.Runner

import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.SortedSet as SS
import Derive.Prelude
import public Data.Linear.Sink
import public FS
import public Test.Async.Spec

%language ElabReflection
%default total

||| A resource handling action (allocation or release of a resource)
public export
data Action : Type -> Type where
  A : (res : a) -> Action a
  R : (res : a) -> Action a

%runElab derive "Action" [Show,Eq]

||| A handled resource.
export
record Handled a where
  constructor H
  value : a

%runElab derive "Handled" [Show,Eq]

export %inline
(.val) : Handled a -> a
(.val) = value

export %inline
(h : Sink (Action a)) => Resource (Async e) (Handled a) where
  cleanup v = lift1 $ h.sink (R v.val)

export %inline
alloc : (h : Sink (Action a)) => a -> Async e es (Handled a)
alloc v = lift1 (h.sink (A v)) $> H v

export %inline
allocNat : Sink (Action Nat) => Nat -> Async e es (Handled Nat)
allocNat = alloc

public export
data Event : (r,o : Type) -> Type where
  Out     : (val : o) -> Event r o
  Alloc   : (res : r) -> Event r o
  Release : (res : r) -> Event r o

%runElab derive "Event" [Show,Eq]

export %inline
unalloc : Event r o -> Maybe r
unalloc (Alloc ev) = Just ev
unalloc _          = Nothing

export %inline
unrelease : Event r o -> Maybe r
unrelease (Release ev) = Just ev
unrelease _            = Nothing

export %inline
unout : Event r o -> Maybe o
unout (Out v) = Just v
unout _       = Nothing

export
Cast (Action r) (Event r o) where
  cast (A v) = Alloc v
  cast (R v) = Release v

public export
record Runres (es : List Type) (e,o,r : Type) where
  constructor RR
  result : Outcome es r
  events : List (Event e o)

export %inline
succeed : r -> List (Event e o) -> Runres es e o r
succeed res = RR (Succeeded res)

export %inline
failed : Has x es => x -> List (Event e o) -> Runres es e o r
failed err = RR (Error $ inject err)

export %inline
succeed' : List (Event e o) -> Runres es e o ()
succeed' = succeed ()

export
All Eq es => Eq e => Eq o => Eq r => Eq (Runres es e o r) where
  RR r1 e1 == RR r2 e2 = r1 == r2 && e1 == e2

export
All Show es => Show e => Show o => Show r => Show (Runres es e o r) where
  showPrec p (RR r e) = showCon p "RR" (showArg r ++ showArg e)

export %inline
allocSink : Sink (Event r o) -> Sink (Action r)
allocSink = cmap cast

export %inline
outputSink : Sink (Event r o) -> Sink o
outputSink = cmap Out

export covering
testStream :
     (0 ev,o : Type)
  -> (Sink (Action ev) => Sink o => AsyncPull e Void es r)
  -> Async e [] (Runres es ev o r)
testStream ev o s = do
  (sink, getVals) <- lift1 $ snocSink1 (Event ev o)
  out <- pull (s @{allocSink sink} @{outputSink sink})
  vs  <- lift1 $ getVals
  pure (RR out vs)

||| Specialized version of `testStream`.
export covering %inline
testNN :
     (Sink (Action Nat) => Sink Nat => AsyncPull e Void es r)
  -> Async e [] (Runres es Nat Nat r)
testNN = testStream Nat Nat

export %inline
toSink : LIO (f es) => (s : Sink o) => Pull f o es r -> Pull f Void es r
toSink = foreach (lift1 . s.sink)

export %inline
sinkAll : LIO (f es) => (s : Sink o) => Pull f (List o) es r -> Pull f Void es r
sinkAll = foreach (lift1 . traverse1_ s.sink)

export
acquired : Runres es ev o r -> List ev
acquired = mapMaybe unalloc . events

export
released : Runres es ev o r -> List ev
released = mapMaybe unrelease . events

export
notReleased : Ord ev => Runres es ev o r -> List ev
notReleased x = go [<] (sort $ acquired x) (sort $ released x)
  where
    go : SnocList ev -> (aq,rel : List ev) -> List ev
    go sx aq      []      = sx <>> aq
    go sx []      _       = sx <>> []
    go sx (a::as) (r::rs) =
      case compare a r of
        EQ => go sx as rs
        LT => go (sx:<a) as (r::rs)
        GT => go sx (a::as) rs

export
first : List o -> Maybe o
first (h::_) = Just h
first []     = Nothing

export
last : List o -> Maybe o
last [v]     = Just v
last (_::vs) = last vs
last []      = Nothing

export
output : Runres es ev o r -> List o
output = mapMaybe unout . events

export
error : Runres es ev o r -> Maybe (HSum es)
error x =
  case x.result of
    Error err => Just err
    _         => Nothing

export
success : Runres es ev o r -> Maybe r
success x =
  case x.result of
    Succeeded v => Just v
    _           => Nothing

export
canceled : Runres es ev o r -> Bool
canceled x =
  case x.result of
    Canceled => True
    _        => False

parameters {0 es  : List Type}
           {0 o,r : Type}
           (0 ev  : Type)
           (p     : Sink (Action ev) => AsyncPull e o es r)

  export covering
  assertPull : Show a => Eq a => (Runres es ev o r -> a) -> (exp : a) -> Test e
  assertPull get = assert (get <$> testStream ev o (toSink p))

  export covering %inline
  assertOut : Show o => Eq o => (exp : List o) -> Test e
  assertOut = assertPull output

  export covering %inline
  assertSorted : Show o => Ord o => (exp : List o) -> Test e
  assertSorted = assertPull (sort . output)

  export covering %inline
  assertSet : Show o => Ord o => (exp : SortedSet o) -> Test e
  assertSet = assertPull (SS.fromList . output)

  export covering %inline
  assertAcquired : Show ev => Eq ev => (exp : List ev) -> Test e
  assertAcquired = assertPull acquired

  export covering %inline
  assertSortedAcquired : Show ev => Ord ev => (exp : List ev) -> Test e
  assertSortedAcquired = assertPull (sort . acquired)

  export covering %inline
  assertReleased : Show ev => Eq ev => (exp : List ev) -> Test e
  assertReleased = assertPull released

  export covering %inline
  assertSortedReleased : Show ev => Ord ev => (exp : List ev) -> Test e
  assertSortedReleased = assertPull (sort . released)

  export covering %inline
  assertLastReleased : Show ev => Eq ev => (exp : Maybe ev) -> Test e
  assertLastReleased = assertPull (last . released)

  export covering %inline
  assertFirstReleased : Show ev => Eq ev => (exp : Maybe ev) -> Test e
  assertFirstReleased = assertPull (first . released)

  export covering %inline
  assertEvents : Show o => Eq o => Show ev => Eq ev => List (Event ev o) -> Test e
  assertEvents = assertPull events

  export covering %inline
  assertErr : Has x es => All Show es => All Eq es => x -> Test e
  assertErr = assertPull error . Just . inject

  export covering %inline
  assertSuccess : Show r => Eq r => r -> Test e
  assertSuccess = assertPull success . Just

  export covering %inline
  assertCanceled : Test e
  assertCanceled = assertPull canceled True

  export covering %inline
  assertReleasedAll : Show ev => Ord ev => Test e
  assertReleasedAll = assertPull notReleased []
