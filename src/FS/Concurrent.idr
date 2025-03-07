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
import FS.Pull
import FS.Scope

import IO.Async.BQueue
import IO.Async.Channel
import IO.Async.Loop.TimerH
import IO.Async.Semaphore

import public FS.Stream
import public IO.Async

||| Convenience alias for `Pull World . Async`
public export
0 AsyncPull : Type -> Type -> List Type -> Type -> Type
AsyncPull e = Pull World (Async e)

||| Convenience alias for `Stream World . Async`
public export
0 AsyncStream : Type -> List Type -> Type -> Type
AsyncStream e = Stream World (Async e)

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
      pull (interruptOn (await doneR) str)

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

parameters (chnl : Channel (List o))
           (done : Deferred World ())
           (res  : Deferred World (Result es ()))
           (sema : IORef Nat)

  -- Handles the outcome of running one of the input streams.
  -- in case the stream terminated with an error, `res` is immediately
  -- set, which causes the output stream to be interrupted and refire
  -- the error. Otherwise, the counter in `sema` is atomically reduced
  -- bye one and the channel closed if the counter arrives at 0.
  out : Outcome es () -> Async e [] ()
  out (Error err) = putDeferred res (Left err)
  out _           = do
    0 <- update sema (\x => let y := pred x in (y,y)) | _ => pure ()
    close chnl

  -- Starts running one of the input streams `s` in the background, returning
  -- the corresponding fiber. Running `s` is interrupted if
  -- the output stream is exhausted and `done` is completed.
  -- The running input stream writes all chunks of output to the channel.
  child : AsyncStream e es o -> Async e es (Fiber [] ())
  child s =
       evalMapChunk (map pure . send chnl) s
    |> takeWhile (== Sent)
    |> drain
    |> parrunCase (await done) out

  -- starts running all input streams in parallel, and reads chunks of
  -- output from the bounded queue `que`.
  merged : List (AsyncStream e es o) -> AsyncStream e es o
  merged ss = S $ do
    _ <- acquire (traverse child ss) (\fs => putDeferred done () >> traverse_ wait fs)
    Till (await res >>= fromResult) (pull $ receive chnl)

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
merge [s] = s
merge ss  =
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
    pure (merged chnl done res sema ss)

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

parameters (done      : Deferred World ())
           (available : Semaphore)
           (running   : SignalRef Nat)
           (output    : Channel (List o))

  %inline
  decRunning : Async e es ()
  decRunning =
    updateAndGet running pred >>= \case
      0 => close output
      _ => pure ()

  inner : AsyncStream e [] o -> Async e es (Fiber [] ())
  inner s = do
    acquire available
    _ <- updateAndGet running S
    parrun
      (await done)
      (decRunning >> release available)
      (foreachChunk (ignore . send output) s)

  outer : AsyncStream e [] (AsyncStream e [] o) -> Async e [] (Fiber [] ())
  outer ss =
    start $
      guarantee
        (run $ foreach (ignore . inner) ss)
        (putDeferred done () >> decRunning)

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
||| When the outer stream fails, evaluation of all inner streams is interrupted
||| and the resulting stream will fail with same failure.
|||
||| When any of the inner streams fail, then the outer stream and all other inner
||| streams are interrupted, resulting in stream that fails with the error of the
||| stream that caused initial failure.
|||
||| Finalizers on each inner stream are run at the end of the inner stream,
||| concurrently with other stream computations.
|||
||| Finalizers on the outer stream are run after all inner streams have been pulled
||| from the outer stream but not before all inner streams terminate -- hence finalizers on the outer stream will run
||| AFTER the LAST finalizer on the very last inner stream.
|||
||| Finalizers on the returned stream are run after the outer stream has finished
||| and all open inner streams have finished.
export
parJoin :
     (maxOpen    : Nat)
  -> {auto 0 prf : IsSucc maxOpen}
  -> (outer      : AsyncStream e [] (AsyncStream e [] o))
  -> AsyncStream e [] o
parJoin maxOpen outer =
  force $ do
    -- signals exhaustion of the output stream (for instance, due
    -- to a `take n`). It will interrupt evaluation of the
    -- input stream and all child streams.
    done      <- deferredOf {s = World} ()

    -- concurrent slots available. child streams will wait on this
    -- before being started.
    available <- semaphore maxOpen

    running   <- signal (S Z)

    -- the input channel used for the result stream. it will be
    -- closed when the last child was exhausted.
    output    <- channelOf (List o) 0

    -- the resulting stream should cleanup resources when it is done.
    -- it should also finalize `done`.
    pure $ do
      _ <- resource (pure ())
      receive output)
