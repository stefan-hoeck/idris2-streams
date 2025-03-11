||| This module provides combinators for running streams concurrently,
||| merging the output they produce nondeterministically, or interrupting
||| a stream after a timeout.
|||
||| Unlike the combinators in `FS.Stream`, we need a concurrent runtime
||| to use the combinators provided here, which means that they run in
||| the `Async` monad.
module FS.Concurrent

import Data.Linear.Deferred
import Data.Linear.Ref1
import Data.Maybe

import FS.Concurrent.Signal
import FS.Concurrent.Util
import FS.Pull
import FS.Scope

import IO.Async.BQueue
import IO.Async.Channel
import IO.Async.Loop.TimerH
import IO.Async.Semaphore

import public FS.Stream
import public IO.Async

%default total

||| Convenience alias for `Pull . Async`
public export
0 AsyncPull : Type -> Type -> List Type -> Type -> Type
AsyncPull e = Pull (Async e)

||| Convenience alias for `Stream . Async`
public export
0 AsyncStream : Type -> List Type -> Type -> Type
AsyncStream e = Stream (Async e)

||| An empty stream that terminates after the given delay.
export %inline
sleep : TimerH e => Clock Duration -> AsyncStream e es o
sleep = exec . sleep

||| Emits the given value after a delay of the given duration.
export %inline
delayed : TimerH e => Clock Duration -> o -> AsyncStream e es o
delayed dur v = sleep dur <+> pure v

--------------------------------------------------------------------------------
-- Streams from Concurrency Primitives
--------------------------------------------------------------------------------

||| Converts a bounded queue of chunks into an infinite stream
||| of values.
export %inline
dequeue : BQueue (List o) -> AsyncStream e es o
dequeue = repeat . evals . dequeue

||| Converts a channel of chunks into an infinite stream of values.
export %inline
receive : Channel (List o) -> AsyncStream e es o
receive = unfoldEvalChunk . receive

--------------------------------------------------------------------------------
-- Interrupting Streams
--------------------------------------------------------------------------------

||| Interrupts the given stream when the given asynchronous
||| computation completes.
export %inline
interruptOn : Deferred World a -> AsyncStream e es o -> AsyncStream e es o
interruptOn check (S p) = S (interruptPull check p)

||| Runs the first stream until it terminates or the second
||| stream emits a `True`.
export
interruptWhen :
     AsyncStream e es o
  -> AsyncStream e [] Bool
  -> AsyncStream e es o
interruptWhen str stop = do
  sc <- currentScope
  force $ do
    doneL <- deferredOf ()
    doneR <- deferredOf ()
    let watcher := foreachChunk (\_ => putDeferred doneR ()) (any id stop)
    pure $ bracket
      (assert_total $ parrun sc doneL (pure ()) watcher)
      (\f => putDeferred doneL () >> wait f)
      (\_ => interruptOn doneR str)

||| Runs the given stream until the given duration expires.
export
timeout : TimerH e => Clock Duration -> AsyncStream e es o -> AsyncStream e es o
timeout dur str = S $ do
  def <- deferredOf ()
  _   <- acquire (start {es = []} $ sleep dur >> putDeferred def ()) cancel
  pull (interruptOn def str)

--------------------------------------------------------------------------------
-- Merging Streams
--------------------------------------------------------------------------------

parameters (chnl : Channel (List o))
           (done : Deferred World ())
           (res  : Deferred World (Result es ()))
           (sema : IORef Nat)
           (sc   : Scope (Async e))

  -- Handles the outcome of running one of the input streams.
  -- in case the stream terminated with an error, `res` is immediately
  -- set, which causes the output stream to be interrupted and refire
  -- the error. Otherwise, the counter in `sema` is atomically reduced
  -- bye one and the channel closed if the counter arrives at 0.
  out : Outcome es () -> Async e [] ()
  out (Error err) = putDeferred res (Left err)
  out _           = do
    0 <- update sema (\x => let y := pred x in (y,y)) | _ => pure ()
    putStrLn "Channel closed"
    close chnl

  -- Starts running one of the input streams `s` in the background, returning
  -- the corresponding fiber. Running `s` is interrupted if
  -- the output stream is exhausted and `done` is completed.
  -- The running input stream writes all chunks of output to the channel.
  covering
  child : AsyncStream e es o -> Async e es (Fiber [] ())
  child s = foreachChunk (ignore . send chnl) s |> parrunCase sc done out

  -- starts running all input streams in parallel, and reads chunks of
  -- output from the bounded queue `que`.
  merged : List (AsyncStream e es o) -> AsyncStream e es o
  merged ss =
    assert_total $
      bracket
        (traverse child ss)
        (\fs => putDeferred done () >> traverse_ wait fs)
        (\_  => interruptOn res (receive chnl))

||| Runs the given streams in parallel and nondeterministically
||| (but chunkc-wise) interleaves their output.
|||
||| The resulting stream will emit chunks as long as one of the input
||| streams is still alive, or until one of the input streams terminates
||| with an error, in which case the output stream will terminate with
||| the same error.
export
merge : List (AsyncStream e es o) -> AsyncStream e es o
merge []  = neutral
merge ss  = Prelude.do
  sc <- currentScope
  force $ Prelude.do
    -- A bounded queue where the running streams will write their output
    -- to. There will be no buffering: evaluating the streams will block
    -- until then next chunk of ouptut has been requested by the consumer.
    chnl <- channelOf (List o) 0

    -- Signals the exhaustion of the output stream, which will cause all
    -- input streams to be interrupted.
    done <- deferredOf {s = World} ()

    -- Signals the termination of the input streams. This will be set as
    -- soon as one input stream throws an error, or after all input
    -- streams terminated successfully.
    res  <- deferredOf {s = World} (Result es ())

    -- Semaphore-like counter keeping track of the number of input streams
    -- that are still running.
    sema <- newref (length ss)
    pure (merged chnl done res sema sc ss)

||| Runs the given streams in parallel and nondeterministically interleaves
||| their output.
|||
||| This will terminate as soon as the first string is exhausted.
export
mergeHaltL : (s1,s2 : AsyncStream  e es o) -> AsyncStream e es o
mergeHaltL s1 s2 = takeWhileJust $ merge [endWithNothing s1, map Just s2]

||| Runs the given streams in parallel and nondeterministically interleaves
||| their output.
|||
||| This will terminate as soon as either stream is exhausted.
export
mergeHaltBoth : (s1,s2 : AsyncStream  e es o) -> AsyncStream e es o
mergeHaltBoth s1 s2 =
  takeWhileJust $ merge [endWithNothing s1, endWithNothing s2]

--------------------------------------------------------------------------------
-- Parallel Joining of Streams
--------------------------------------------------------------------------------

-- `parJoin` implementation
parameters (done      : Deferred World (Result es ()))
           (available : Semaphore)
           (running   : SignalRef Nat)
           (output    : Channel (List o))
           (sc        : Scope (Async e))

  -- Every time an inner or the outer stream terminates, the number
  -- of running fibers is reduced by one. If this reaches zero, no
  -- more streams (including the outer stream!) is running, so the
  -- channel can be closed. The result stream will terminated as soon
  -- as the closed channel is empty.
  %inline
  decRunning : Async e [] ()
  decRunning =
    updateAndGet running pred >>= \case
      0 => close output
      _ => pure ()

  -- Runs an inner stream on its own fiber until it terminates gracefully
  -- or fails with an error. In case of an error, the `done` flag is set
  -- immediately to hold the error and stop all other running streams.
  covering
  inner : AsyncStream e es o -> Async e es ()
  inner s =
    uncancelable $ \poll => do
      poll (acquire available) -- wait for a fiber to become available
      modify running S         -- increase the number of running fibers
      poll $ ignore $ parrunCase sc
        done
        (\o => putErr done o >> decRunning >> release available)
        (foreachChunk (ignore . send output) s)

  -- Runs the outer stream on its own fiber until it terminates gracefully
  -- or fails with an error.
  -- The stream is interrupted as soon as the `done` flag is set.
  covering
  outer : AsyncStream e es (AsyncStream e es o) -> Async e es (Fiber [] ())
  outer ss =
    parrunCase sc
      done
      (\o => putErr done o >> decRunning >> until running (== 0))
      (foreach (inner . scope) ss)

||| Nondeterministically merges a stream of streams (`outer`) in to a single stream,
||| opening at most `maxOpen` streams at any point in time.
|||
||| The outer stream is evaluated and each resulting inner stream is run concurrently,
||| up to `maxOpen` stream. Once this limit is reached, evaluation of the outer stream
||| is paused until one or more inner streams finish evaluating.
|||
||| When the outer stream stops gracefully, all inner streams continue to run,
||| resulting in a stream that will stop when all inner streams finish
||| their evaluation.
|||
||| Finalizers on each inner stream are run at the end of the inner stream,
||| concurrently with other stream computations.
|||
||| Finalizers on the outer stream are run after all inner streams have been pulled
||| from the outer stream but not before all inner streams terminate
||| -- hence finalizers on the outer stream will run
||| AFTER the LAST finalizer on the very last inner stream.
|||
||| Finalizers on the returned stream are run after the outer stream has finished
||| and all open inner streams have finished.
export
parJoin :
     (maxOpen    : Nat)
  -> {auto 0 prf : IsSucc maxOpen}
  -> (outer      : AsyncStream e es (AsyncStream e es o))
  -> AsyncStream e es o
parJoin maxOpen out = do
  sc <- currentScope
  assert_total $ force $ do
    -- signals exhaustion of the output stream (for instance, due
    -- to a `take n`). It will interrupt evaluation of the
    -- input stream and all child streams.
    done      <- deferredOf {s = World} (Result es ())

    -- concurrent slots available. child streams will wait on this
    -- before being started.
    available <- semaphore maxOpen

    running   <- signal 1

    -- the input channel used for the result stream. it will be
    -- closed when the last child was exhausted.
    output    <- channelOf (List o) 0

    fbr       <- outer done available running output sc out
    -- the resulting stream should cleanup resources when it is done.
    -- it should also finalize `done`.
    pure $
      finally
        (putDeferred done (Right ()) >> wait fbr)
        (interruptOn done (receive output))
