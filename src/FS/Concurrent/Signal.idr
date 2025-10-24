module FS.Concurrent.Signal

import Data.Linear.Deferred
import Data.Linear.Ref1
import Data.Linear.Traverse1

import FS.Pull

import IO.Async

%default total

record ST a where
  constructor S
  value     : a
  last      : Nat
  listeners : List (Once World (a,Nat))

%inline
putImpl : a -> ST a -> (ST a, IO1 ())
putImpl v (S _ lst []) = (S v (S lst) [], (() # ))
putImpl v (S _ lst ls) =
  let n := S lst
   in (S v n [], traverse1_ (\o => putOnce1 o (v,n)) ls)

%inline
updImpl : (a -> (a,b)) -> ST a -> (ST a, IO1 b)
updImpl f (S cur lst ls) =
  let n     := S lst
      (v,r) := f cur
   in ( S v n []
      , \t => let _ # t := traverse1_ (\o => putOnce1 o (v,n)) ls t in r # t
      )

%inline
nextImpl :
     Poll (Async e)
  -> Nat
  -> Once World (a,Nat)
  -> ST a
  -> (ST a, Async e es (a,Nat))
nextImpl poll last once st@(S v lst ls) =
  case last == lst of
    False => (st, pure (v,lst))
    True  => (S v lst (once :: ls), poll (awaitOnce once))

public export
record SignalRef a where
  constructor SR
  ref : Ref World (ST a)

||| An observable, mutable value
export
signal : Lift1 World f => a -> f (SignalRef a)
signal v = SR <$> newref (S v 1 [])

||| Reads the current value of the signal.
export %inline
get : Lift1 World f => SignalRef a -> f a
get (SR ref) = value <$> readref ref

||| Writes the current value to the signal.
export
put : Lift1 World f => SignalRef a -> (v : a) -> f ()
put (SR ref) v = do
  act <- update ref (putImpl v)
  lift1 act

||| Updates the value stored in the signal with the given function
||| and returns the second result of the computation.
export
update : Lift1 World f => SignalRef a -> (g : a -> (a,b)) -> f b
update (SR ref) g = do
  act <- update ref (updImpl g)
  lift1 act

||| Updates the value stored in the signal.
export %inline
modify : Lift1 World f => SignalRef a -> (g : a -> a) -> f ()
modify s g = update s (\v => (g v, ()))

||| Updates the value stored in the signal and returns the result.
export %inline
updateAndGet : Lift1 World f => SignalRef a -> (g : a -> a) -> f a
updateAndGet s g = update s (\v => let w := g v in (w,w))

||| Awaits the next value and its count, potentially blocking the
||| current fiber if the internal counter is at `current`.
|||
||| Note: The internal counter starts at `1`, so invoking this with
|||       a count of `0` will always immediately return the internal
|||       value and count.
export
next : SignalRef a -> Nat -> Async e es (a,Nat)
next (SR ref) n = do
  def <- onceOf (a,Nat)
  uncancelable $ \poll => do
    act <- update ref (nextImpl poll n def)
    act

||| Creates a continuous stream of values that reads the current
||| value every time a value is pulled from the stream.
export %inline
continuous : SignalRef a -> Pull (Async e) a es ()
continuous = repeat . eval . get

||| Creates a discrete stream of values that reads the current
||| value every time it changes.
|||
||| Note: There is no buffering of values. If the signal is updated
|||       more quickly than the stream is being pulled, some values
|||       might be lost.
export %inline
discrete : SignalRef a -> Pull (Async e) a es ()
discrete s = unfoldEval 0 (map (uncurry More). next s)

||| Blocks the fiber and observes the given signal until the given
||| predicate returns `True`.
export covering
until : SignalRef a -> (a -> Bool) -> Async e [] ()
until ref pred = discrete ref |> any pred |> drain |> mpull
