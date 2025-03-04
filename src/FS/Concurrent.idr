module FS.Concurrent

import Data.Linear.Deferred
import Data.Linear.Ref1
import Data.Maybe

import FS.Pull
import FS.Scope
import IO.Async.BQueue
import IO.Async.Loop.TimerH
import IO.Async.Semaphore

import public FS.Stream
import public IO.Async

public export
0 AsyncPull : Type -> Type -> List Type -> Type -> Type
AsyncPull e = Pull World (Async e)

public export
0 AsyncStream : Type -> List Type -> Type -> Type
AsyncStream e = Stream World (Async e)

||| An empty stream that terminates after the given duration.
export %inline
sleep : TimerH e => Clock Duration -> AsyncStream e es ()
sleep = eval . sleep

--------------------------------------------------------------------------------
-- Interrupting Streams
--------------------------------------------------------------------------------

||| Interrupts the given stream when the given asynchronous
||| computation completes.
export %inline
interruptOn : Async e es () -> AsyncStream e es o -> AsyncStream e es o
interruptOn check (S p) = S (Till check p)

||| Interrupts the given stream when the given `Deferred` is completed.
export %inline
tillDeferred : Deferred World () -> AsyncStream e es o -> AsyncStream e es o
tillDeferred = interruptOn . await

||| Interrupts the given stream when the given `Deferred` is completed.
export %inline
tillSemaphore : Semaphore -> AsyncStream e es o -> AsyncStream e es o
tillSemaphore = interruptOn . await

||| Runs the first stream until it terminates or the second
||| stream emits a `True`.
export
interruptWhen :
     AsyncStream e es o
  -> AsyncStream e [] Bool
  -> AsyncStream e es o
interruptWhen str stop =
  force $ do
    doneL <- deferredOf ()
    doneR <- deferredOf ()
    pure (watched doneL doneR)

  where
    watcher : (doneL, doneR : Deferred World ()) -> Async e [] ()
    watcher doneL doneR =
      guarantee
        (run $ ignore $ tillDeferred doneL $ any id stop)
        (putDeferred doneR ())

    watched : (doneL, doneR : Deferred World ()) -> AsyncStream e es o
    watched doneL doneR = S $ do
      _ <- acquire (start $ watcher doneL doneR) (\f => putDeferred doneL () >> wait f)
      pull (tillDeferred doneR str)

||| Runs the given stream until the given duration expires.
export
timeout : TimerH e => Clock Duration -> AsyncStream e es o -> AsyncStream e es o
timeout dur str = S $ do
  def <- deferredOf ()
  _   <- acquire (start {es = []} $ sleep dur >> putDeferred def ()) cancel
  Till (await def) str.pull

--------------------------------------------------------------------------------
-- Merging Streams
--------------------------------------------------------------------------------

||| Runs the two given streams in parallel and non-deterministically
||| interleaves their output. TODO: Not yet done.
export
merge : AsyncStream e es o -> AsyncStream e es o -> AsyncStream e es o
merge s1 s2 =
  force $ Prelude.do
    que  <- bqueueOf (List o) 0
    done <- deferredOf {s = World} ()
    sema <- semaphore 2
    pure $ tillSemaphore sema (repeat $ evals (dequeue que))
