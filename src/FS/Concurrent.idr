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

||| Concurrently runs the given stream until it either terminates or
||| is interrupted by `check`.
|||
||| This is a low-level utility used to implement the combinators in this
||| module. It is exported, because it might be useful when
||| implementing other combinators,
export
parrunCase :
     (check   : Async e fs ())
  -> (finally : Outcome fs () -> Async e [] ())
  -> AsyncStream e fs ()
  -> Async e es (Fiber [] ())
parrunCase check finally s =
  start $ dropErrs $ guaranteeCase (run $ interruptOn check s) finally

||| Concurrently runs the given stream until it either terminates or
||| is interrupted by `check`.
|||
||| This is a low-level utility used to implement the combinators in this
||| module. It is exported, because it might be useful when
||| implementing other combinators,
export %inline
parrun :
     (check   : Async e fs ())
  -> (finally : Async e [] ())
  -> AsyncStream e fs ()
  -> Async e es (Fiber [] ())
parrun check = parrunCase check . const

||| Interrupts the given stream when the given `Deferred` is completed.
export %inline
tillDeferred : Deferred World () -> AsyncStream e es o -> AsyncStream e es o
tillDeferred = interruptOn . await

||| Interrupts the given stream when the given `Semaphore` is completed.
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
    watched : (doneL, doneR : Deferred World ()) -> AsyncStream e es o
    watched doneL doneR = S $ do
      let watcher := parrun (await doneL) (putDeferred doneR ()) (ignore $ any id stop)
      _ <- acquire watcher (\f => putDeferred doneL () >> wait f)
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

parameters (que  : BQueue (List o))
           (done : Deferred World ())
           (res  : Deferred World (Result es ()))
           (sema : IORef Nat)

  -- Handles the outcome of running one of the input streams.
  -- in case the stream terminated with an error, `res` is immediately
  -- set, which causes the output stream to be interrupted and refire
  -- the error. Otherwise, the counter in `sema` is atomically reduced
  -- bye one nad `res` set to `Right ()` in case the counter arrives
  -- at 0.
  out : Outcome es () -> Async e [] ()
  out (Error err) = putDeferred res (Left err)
  out _           = do
    0 <- update sema (\x => let y := pred x in (y,y)) | _ => pure ()
    putDeferred res (Right ())

  -- Starts running one of the input streams `s` in the background, returning
  -- the corresponding fiber. Running `s` is interrupted if
  -- the output stream is exhausted and `done` is completed.
  -- The running input stream writes all chunks of output to the given
  -- bounded queue.
  child : AsyncStream e es o -> Async e es (Fiber [] ())
  child = parrunCase (await done) out . sinkChunks (enqueue que)

  -- starts running all input streams in parallel, and reads chunks of
  -- output from the bounded queue `que`.
  merged : List (AsyncStream e es o) -> AsyncStream e es o
  merged ss = S $ do
    _ <- acquire (traverse child ss) (\fs => putDeferred done () >> traverse_ wait fs)
    Till (await res >>= fromResult) (pull $ repeat $ evals (dequeue que))

||| Runs the given streams in parallel and non-deterministically
||| (but chunkc-wise) interleaves their output.
|||
||| The resulting stream will emit chunks as long as one of the input
||| streams is still alive, or until one of the input streams terminates
||| with an error, in which case the output stream will terminated with
||| the same error.
export
merge : List (AsyncStream e es o) -> AsyncStream e es o
merge []  = neutral
merge [s] = s
merge ss  =
  force $ Prelude.do
    que  <- bqueueOf (List o) 0
    done <- deferredOf {s = World} ()
    res  <- deferredOf {s = World} (Result es ())
    sema <- newref (length ss)
    pure (merged que done res sema ss)
