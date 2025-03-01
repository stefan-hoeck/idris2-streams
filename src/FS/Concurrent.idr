module FS.Concurrent

import Data.Linear.Deferred
import Data.Linear.Ref1
import Data.Maybe

import FS.Pull
import FS.Scope
import IO.Async.Loop.TimerH

import public FS.Stream
import public IO.Async

public export
0 AsyncStream : Type -> List Type -> Type -> Type
AsyncStream e = Stream World (Async e)

export
interruptEvals : Async e es (List o) -> AsyncStream e es o
interruptEvals act =
  S $ do
    sc <- scope
    pull $ evals (fromMaybe [] <$> race [act, await sc.interrupted $> []])

export %inline
interruptEval : Async e es o -> AsyncStream e es o
interruptEval = interruptEvals . map pure

export %inline
sleep : TimerH e => Clock Duration -> AsyncStream e es ()
sleep = interruptEval . sleep

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
        (run $ ignore $ interruptOn doneL $ any id stop)
        (putDeferred doneR ())

    watched : (doneL, doneR : Deferred World ()) -> AsyncStream e es o
    watched doneL doneR = S $ do
      _ <- acquire (start $ watcher doneL doneR) (\f => putDeferred doneL () >> wait f)
      pull (interruptOn doneR str)

export
timeout : TimerH e => Clock Duration -> AsyncStream e es o -> AsyncStream e es o
timeout dur str = str `interruptWhen` (sleep dur $> True)
