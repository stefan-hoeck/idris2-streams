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
0 AsyncPull : Type -> Type -> List Type -> Type -> Type
AsyncPull e = Pull World (Async e)

public export
0 AsyncStream : Type -> List Type -> Type -> Type
AsyncStream e = Stream World (Async e)

||| Interrupts the given stream when the given check returns `True`.
export %inline
interruptOn :
     Deferred World ()
  -> AsyncStream s es o
  -> AsyncStream s es o
interruptOn check (S p) = S (Till check p)

export %inline
sleep : TimerH e => Clock Duration -> AsyncStream e es ()
sleep = eval . sleep

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
timeout dur str = S $ do
  def <- deferredOf ()
  _   <- acquire (start {es = []} $ sleep dur >> putDeferred def ()) (\f => cancel f)
  Till def str.pull
