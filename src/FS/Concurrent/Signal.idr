module FS.Concurrent.Signal

import Data.Linear.Deferred
import Data.Linear.Ref1

import FS.Stream

import IO.Async

%default total

record ST a where
  constructor S
  value     : a
  last      : Nat
  listeners : List (Once World (a,Nat))

%inline
putImpl : a -> ST a -> (ST a, Async e es ())
putImpl v (S _ lst []) = (S v (S lst) [], pure ())
putImpl v (S _ lst ls) =
  let n := S lst
   in (S v n [], traverse_ (`putOnce` (v,n)) ls)

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
export %inline
put : SignalRef a -> (v : a) -> Async e es ()
put (SR ref) v = do
  act <- update ref (putImpl v)
  act

||| Awaits the next value and its count, potentially blocking the
||| current fiber if the internal counter is at `current`.
|||
||| Note: The internal counter starts at `1`, so invoking this with
|||       a count of `0` will always immediately return the internal
|||       value and count.
export %inline
next : SignalRef a -> Nat -> Async e es (a,Nat)
next (SR ref) n = do
  def <- onceOf (a,Nat)
  uncancelable $ \poll => do
    act <- update ref (nextImpl poll n def)
    act

||| Creates a continuous stream of values that reads the current
||| value every time a value is pulled from the stream.
export %inline
continuous : SignalRef a -> Stream World (Async e) es a
continuous = repeat . eval . get

||| Creates a discrete stream of values that reads the current
||| value every time it changes.
|||
||| Note: There is no buffering of values. If the signal is updated
|||       more quickly than the stream is being pulled, some values
|||       might be lost.
export %inline
discrete : SignalRef a -> Stream World (Async e) es a
discrete s = unfoldEvalST 0 (map Just . next s)
