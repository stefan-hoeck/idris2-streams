module Test.FS.Runner

import Data.Linear.Ref1
import Data.Linear.Traverse1
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

public export
data Event : (r,o : Type) -> Type where
  Out     : (val : o) -> Event r o
  Alloc   : (res : r) -> Event r o
  Release : (res : r) -> Event r o

%runElab derive "Event" [Show,Eq]

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
failed : r -> List (Event e o) -> Runres es e o r

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
