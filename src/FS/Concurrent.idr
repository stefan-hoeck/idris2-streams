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
import Data.List
import Data.Maybe
import Data.Nat

import FS.Concurrent.Signal
import FS.Concurrent.Util
import FS.Pull
import FS.Resource
import FS.Scope

import IO.Async.BQueue
import IO.Async.Channel
import IO.Async.Logging
import IO.Async.Loop.TimerH
import IO.Async.Semaphore

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

||| An empty stream that terminates at the given clock time.
export %inline
waitTill : TimerH e => Clock Monotonic -> AsyncStream e es o
waitTill = exec . waitTill

||| Emits the given value after a delay of the given duration.
export %inline
delayed : TimerH e => Clock Duration -> o -> AsyncStream e es o
delayed dur v = sleep dur >> emit v

||| Emits the given value after at the given clock time
export %inline
atClock : TimerH e => Clock Monotonic -> o -> AsyncStream e es o
atClock dur v = waitTill dur >> emit v

||| Infinitely emits the given value at regular intervals.
export %inline
timed : TimerH e => Clock Duration -> o -> AsyncStream e es o
timed dur v = do
  now <- liftIO (clockTime Monotonic)
  go (addDuration now dur)
  where
    go : Clock Monotonic -> AsyncStream e es o
    go cl = assert_total $ atClock cl v >> go (addDuration cl dur)

||| Emits the values from the given stream, each with a delay of the
||| given duration.
|||
||| The first value will be emitted `after` the given delay.
|||
||| Note: If the given stream emits some values more slowly than specified
|||       by the delays, irregular emission of several values at a time
|||       might be observed.
export
every : TimerH e => Clock Duration -> AsyncStream e es a -> AsyncStream e es a
every x = zipRight (timed x ())

||| Like `every` but the first value will be emitted as soon as the
||| original stream emits it.
export
every0 : TimerH e => Clock Duration -> AsyncStream e es a -> AsyncStream e es a
every0 x = zipRight (cons () $ timed x ())

--------------------------------------------------------------------------------
-- Streams from Concurrency Primitives
--------------------------------------------------------------------------------

||| Converts a bounded queue of values into an infinite stream
||| of values.
export %inline
dequeue : BQueue o -> AsyncStream e es o
dequeue = repeat . eval . dequeue

export %inline
Discrete BQueue where
  discrete = dequeue

||| Converts a channel of chunks into an infinite stream of values.
export %inline
receive : Channel o -> AsyncStream e es o
receive = unfoldEvalMaybe . receive

export %inline
Discrete Channel where
  discrete = receive

--------------------------------------------------------------------------------
-- Interrupting Streams
--------------------------------------------------------------------------------

||| Runs the given stream until the given duration expires.
export
timeout :
     {auto th : TimerH e}
  -> Clock Duration
  -> AsyncStream e es o
  -> AsyncStream e es o
timeout dur str = do
  def <- deferredOf ()
  _   <- acquire (start {es = []} $ sleep dur >> putDeferred def ()) cancel
  interruptOnAny def str

--------------------------------------------------------------------------------
-- Merging Streams
--------------------------------------------------------------------------------

parameters (chnl : Channel o)
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
  child s = foreach (ignore . send chnl) s |> parrunCase done out

  -- Starts running all input streams in parallel, and reads chunks of
  -- output from the bounded queue `que`.
  merged : List (AsyncStream e es o) -> AsyncStream e es o
  merged ss =
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
merge [s] = s
merge ss  = Prelude.do
  -- A bounded queue where the running streams will write their output
  -- to. There will be no buffering: evaluating the streams will block
  -- until then next chunk of ouptut has been requested by the consumer.
  chnl <- channelOf o 0

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

  merged chnl done res sema ss

||| Runs the given streams in parallel and nondeterministically interleaves
||| their output.
|||
||| This will terminate as soon as the first string is exhausted.
export
mergeHaltL : (s1,s2 : AsyncStream e es o) -> AsyncStream e es o
mergeHaltL s1 s2 =
  takeWhileJust $ merge [endWithNothing s1, mapOutput Just s2]

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

upd : Maybe (Async e [] ()) -> (Maybe (Async e [] ()), Bool)
upd Nothing  = (Just $ pure (), True)
upd (Just x) = (Just x, False)

-- `parJoin` implementation
parameters (done      : Deferred World (Result es ()))
           (available : Semaphore)
           (running   : SignalRef Nat)
           (output    : Channel o)
           (leaseref  : Ref World (Maybe $ Async e [] ()))


  doLease : Scope (Async e) -> Async e es ()
  doLease sc = do
    True <- update leaseref upd | False => pure ()
    cl   <- weakenErrors (lease sc)
    writeref leaseref (Just cl)

  doUnlease : Async e [] ()
  doUnlease = readref leaseref >>= sequence_

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
      poll $ ignore $ parrunCase
        done
        (\o => putErr done o >> decRunning >> release available)
        (foreach (ignore . send output) s)

  -- Runs the outer stream on its own fiber until it terminates gracefully
  -- or fails with an error.
  -- The stream is interrupted as soon as the `done` flag is set.
  outer : AsyncStream e es (AsyncStream e es o) -> Async e es (Fiber [] ())
  outer ss =
    parrunCase
      done
      (\o => putErr done o >> decRunning >> until running (== 0) >> doUnlease) $
        flatMap ss $ \v => do
          sc <- scope
          exec (doLease sc >> inner v)

||| Nondeterministically merges a stream of streams (`outer`) in to a single stream,
||| opening at most `maxOpen` streams at any point in time.
|||
||| The outer stream is evaluated and each resulting inner stream is run concurrently,
||| up to `maxOpen` stream. Once this limit is reached, evaluation of the outer stream
||| is paused until one of the inner streams finishes evaluating.
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
parJoin 1       out = flatMap out id
parJoin maxOpen out = do
  leaseref  <- newref {a = Maybe (Async e [] ())} Nothing

  -- Signals exhaustion of the output stream (for instance, due
  -- to a `take n`). It will interrupt evaluation of the
  -- input stream and all child streams.
  done      <- deferredOf (Result es ())

  -- Concurrent slots available. Child streams will wait on this
  -- before being started.
  available <- semaphore maxOpen

  running   <- signal 1

  -- The input channel used for the result stream. It will be
  -- closed when the last child was exhausted.
  output    <- channelOf o 0

  fbr       <- exec $ outer done available running output leaseref out

  -- The resulting stream should cleanup resources when it is done.
  -- It should also finalize `done`.
  finally
    (putDeferred done (Right ()) >> wait fbr)
    (interruptOn done (receive output))

||| Convenience alias for `P.mapOutput inner outer |> parJoin maxOpen`
export %inline
parBind :
     (maxOpen    : Nat)
  -> {auto 0 prf : IsSucc maxOpen}
  -> (inner      : o -> AsyncStream e es p)
  -> (outer      : AsyncStream e es o)
  -> AsyncStream e es p
parBind mo i o = mapOutput i o |> parJoin mo

export
broadcast :
     AsyncStream e es o
  -> (pipes : List (o -> AsyncStream e es p))
  -> {auto 0 prf : NonEmpty pipes}
  -> AsyncStream e es p
broadcast s ps@(_::qs) =
  parJoin (S $ length ps) (flatMap s $ \v => emits $ map ($ v) ps)

||| Uses `parJoin` to map the given function over each emitted output
||| in parallel.
export
parMapE :
     (maxOpen    : Nat)
  -> {auto 0 prf : IsSucc maxOpen}
  -> (fun        : o -> Result es p)
  -> (outer      : AsyncStream e es o)
  -> AsyncStream e es p
parMapE maxOpen fun = parJoin maxOpen . Pull.mapOutput run
  where
    run : o -> AsyncStream e es p
    run o = pure o >>= either fail emit . fun

||| Like `parMapE`, but injects the error first.
export
parMapI :
     {auto has   : Has x es}
  -> (maxOpen    : Nat)
  -> {auto 0 prf : IsSucc maxOpen}
  -> (fun        : o -> Either x p)
  -> (outer      : AsyncStream e es o)
  -> AsyncStream e es p
parMapI maxOpen fun = parMapE maxOpen (mapFst inject . fun)

||| Like `parMapE`, but for a function that cannot fail.
export
parMap :
     (maxOpen    : Nat)
  -> {auto 0 prf : IsSucc maxOpen}
  -> (fun        : o -> p)
  -> (outer      : AsyncStream e es o)
  -> AsyncStream e es p
parMap maxOpen fun = parMapE maxOpen (Right . fun)

export
foreachPar :
     (maxOpen    : Nat)
  -> {auto 0 prf : IsSucc maxOpen}
  -> (sink       : o -> Async e [] ())
  -> (outer      : AsyncPull e o es r)
  -> AsyncPull e q es r
foreachPar maxOpen sink outer = do
  -- Concurrent slots available. Child streams will wait on this
  -- before being started.
  available <- semaphore maxOpen

  finally
    (acquireN available maxOpen)
    (foreach (run available) outer)

  where
    run : Semaphore -> o -> Async e es ()
    run available v = do
      acquire available
      ignore $ start (guarantee (sink v) (release available))

--------------------------------------------------------------------------------
-- Switch Map
--------------------------------------------------------------------------------

parameters (ps    : AsyncStream e es p)
           (guard : Semaphore)

    switchInner : Deferred World () -> AsyncStream e es p
    switchInner halt =
      bracket (acquire guard) (const $ release guard) $ \_ =>
        interruptOnAny halt ps

    switchHalted : IORef (Maybe $ Deferred World ()) -> Async e es (AsyncStream e es p)
    switchHalted ref = do
      halt <- deferredOf ()
      prev <- update ref (Just halt,)
      for_ prev $ \p => putDeferred p ()
      pure $ switchInner halt

||| Like `flatMap` but interrupts the inner stream when
||| new elements arrive in the outer stream.
|||
||| Finializers of each inner stream are guaranteed to run
||| before the next inner stream starts.
||| When the outer stream stops gracefully, the currently running
||| inner stream will continue to run.
|||
||| When an inner stream terminates/interrupts, nothing
||| happens until the next element arrives
||| in the outer stream.
|||
||| When either the inner or outer stream fails, the entire
||| stream fails and the finalizer of the
||| inner stream runs before the outer one.
|||
export
switchMap :
     (o -> AsyncStream e es p)
  -> AsyncStream e es o
  -> AsyncStream e es p
switchMap f os = do
  guard <- semaphore 1
  ref   <- newref Nothing
  parJoin 2 (evalMap (\v => switchHalted (f v) guard ref) os)

--------------------------------------------------------------------------------
-- Hold
--------------------------------------------------------------------------------

public export
record Hold e es o where
  constructor H
  release : Async e [] ()
  stream  : AsyncStream e es o

export %inline
Resource (Async e) (Hold e es o) where
  cleanup = release

||| Converts a discrete stream of values into a continuous one that will
||| emit the last value emitted by the original stream on every pull starting
||| with the given initial value.
|||
||| The original stream is immediately started and
||| processed in the background.
|||
||| This should be used in combination with a call to `bracket` or
||| `resource`, so that the stream running in the background is
||| properly terminated and its resources released
||| once the resulting stream is exhausted.
|||
||| ```idris example
||| signalOn :
|||     o
|||  -> AsyncStream e es ()
|||  -> AsyncStream e es o
|||  -> AsyncStream e es o
||| signalOn ini tick sig =
|||   resource (hold ini sig) (zipRight tick . stream)
||| ```
export
hold :
     (ini : o)
  -> AsyncStream e es o
  -> Async e fs (Hold e es o)
hold ini os = do
  -- Signals the exhaustion of the output stream, which will cause the
  -- input streams to be interrupted.
  done <- deferredOf {s = World} ()

  -- Signals the termination of the input streams. This will be set as
  -- soon as the input stream throws an error or after the input
  -- stream terminated successfully.
  res  <- deferredOf {s = World} (Result es ())

  ref <- newref ini

  fbr <- foreach (writeref ref) os |> parrunCase done (putErr res)
  pure $
    H
      (putDeferred done () >> wait fbr)
      (interruptOn res (repeat (eval $ readref ref)))

||| Like `hold` but the resulting stream will not emit a value
||| until after the original stream first emitted a value.
export
hold1 : AsyncStream e es o -> Async e fs (Hold e es o)
hold1 = map {stream $= catMaybes} . hold Nothing . mapOutput Just

||| Runs the second stream in the background, emitting its latest
||| output whenever the first stream emits.
export
signalOn : o -> AsyncStream e es () -> AsyncStream e es o -> AsyncStream e es o
signalOn ini tick sig = resource (hold ini sig) (zipRight tick . stream)

||| Like `signalOn` but only starts emitting values *after* the
||| second stream emitted its first value.
export
signalOn1 : AsyncStream e es () -> AsyncStream e es o -> AsyncStream e es o
signalOn1 tick sig = resource (hold1 sig) (zipRight tick . stream)

--------------------------------------------------------------------------------
-- Logging Utils
--------------------------------------------------------------------------------

parameters {0 es     : List Type}
           {auto lgs : All Loggable es}
           {auto log : Logger e}

  export
  logExec : (dflt : t) -> Async e es t -> Pull (Async e) o [] t
  logExec dflt = exec . unerr dflt

  export %inline
  tryExec : Async e es t -> Pull (Async e) o [] (Maybe t)
  tryExec = logExec Nothing . map Just

  export
  tryPull : (dflt : r) -> Pull (Async e) o es r -> Pull (Async e) o [] r
  tryPull dflt = handle (mapProperty (\_,v => exec (logLoggable v $> dflt)) lgs)

  export %inline
  tryStream : Stream (Async e) es o -> Stream (Async e) [] o
  tryStream = tryPull ()
