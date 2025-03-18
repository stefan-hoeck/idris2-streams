module FS.Concurrent.Util

import Data.Linear.Deferred
import FS.Pull
import IO.Async

%default total

||| Awaits the completion of a `Deferred`, wrapping the
||| result with the potential of failure.
export %inline
awaitRes : Deferred World (Result es a) -> Async e es a
awaitRes def = await def >>= fromResult

||| Finalizes a deferred in case of an `Error` outcome.
export
putErr : Deferred World (Result es ()) -> Outcome es () -> Async e [] ()
putErr def (Error x) = putDeferred def (Left x)
putErr def _         = pure ()

||| Runs the given pull in a new child scope and interrupts
||| its evaluation once the given `Deferred` is completed.
-- TODO: We should add support for a deferred result plus error
--       handling here.
export
interruptOn :
     Deferred World a
  -> Stream (Async e) es o
  -> Stream (Async e) es o
interruptOn def p = OnIntr (OScope (I def) p) (pure ())

||| Concurrently runs the given stream until it either terminates or
||| is interrupted by `check`.
|||
||| This is a low-level utility used to implement the combinators in this
||| module. It is exported, because it might be useful when
||| implementing other combinators,
-- TODO: We should add support for a deferred result plus error
--       handling here.
export covering
parrunCase :
     (sc      : Scope (Async e))
  -> (check   : Deferred World a)
  -> (finally : Outcome fs () -> Async e [] ())
  -> EmptyStream (Async e) fs
  -> Async e es (Fiber [] ())
parrunCase sc check finally p =
  start $ ignore $ guaranteeCase (pullIn sc $ interruptOn check p) $ \case
    Succeeded res => finally res
    Canceled      => finally Canceled
    Error err impossible

||| Concurrently runs the given stream until it either terminates or
||| is interrupted by `check`.
|||
||| This is a low-level utility used to implement the combinators in this
||| module. It is exported, because it might be useful when
||| implementing other combinators,
-- TODO: We should add support for a deferred result plus error
--       handling here.
export covering %inline
parrun :
     (sc      : Scope (Async e))
  -> (check   : Deferred World a)
  -> (finally : Async e [] ())
  -> EmptyStream (Async e) fs
  -> Async e es (Fiber [] ())
parrun sc check = parrunCase sc check . const
