module Test.FS.Resource

import Data.Linear.Ref1
import Data.Linear.Traverse1
import Derive.Prelude
import FS
import Test.Async.Spec

%language ElabReflection
%default total

public export
data Action : Type -> Type where
  A : (res : a) -> Action a
  R : (res : a) -> Action a

%runElab derive "Action" [Show,Eq]

export
record Handled a where
  constructor H
  value : a

%runElab derive "Handled" [Show,Eq]

export %inline
(.val) : Handled a -> a
(.val) = value

export
record Sink o where
  [noHints]
  constructor S
  sink : o -> IO1 ()

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


public export
record Collector r o where
  [noHints]
  constructor C
  ref : IORef $ SnocList (Event r o)

export
events : HasIO io => Collector r o -> io (List $ Event r o)
events c = (<>> []) <$> runIO (read1 c.ref)

export
allocSink : (c : Collector r o) => Sink (Action r)
allocSink =
  S $ \case
    A v => casmod1 c.ref (:< Alloc v)
    R v => casmod1 c.ref (:< Release v)

export
outputSink : (c : Collector r o) => Sink o
outputSink = S $ \v => casmod1 c.ref (:< Out v)

export %inline
writeOutput : Lift1 World f => (h : Sink o) => List o -> f ()
writeOutput = lift1 . traverse1_ h.sink

--------------------------------------------------------------------------------
-- Spec
--------------------------------------------------------------------------------

parameters {auto sr : Sink (Action Nat)}
           {auto so : Sink Nat}

  natStream : Nat -> AsyncStream e [] Void
  natStream x = do
    n <- acquire (alloc x) cleanup
    C.iterate (List Nat) n.val S |> foreach writeOutput

export covering
testStream :
     (0 r,o : Type)
  -> (Collector r o => AsyncStream e es Void)
  -> Async e [] (Outcome es (List $ Event r o))
testStream r o s = do
  ref <- newref [<]
  out <- pull (s @{C ref})
  se  <- readref ref
  pure (out $> (se <>> []))
