module FS.Concurrent.Util

import Data.Linear.Deferred
import FS.Pull
import FS.Stream
import FS.Target
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

||| Concurrently runs the given stream until it either terminates or
||| is interrupted by `check`.
|||
||| This is a low-level utility used to implement the combinators in this
||| module. It is exported, because it might be useful when
||| implementing other combinators,
export covering
parrunCase :
     (check   : Async e fs ())
  -> (finally : Outcome fs () -> Async e [] ())
  -> Stream (Async e) fs ()
  -> Async e es (Fiber [] ())
parrunCase check finally (S p) =
  start $ dropErrs $ guaranteeCase (run $ S $ Till check p) finally

||| Concurrently runs the given stream until it either terminates or
||| is interrupted by `check`.
|||
||| This is a low-level utility used to implement the combinators in this
||| module. It is exported, because it might be useful when
||| implementing other combinators,
export covering %inline
parrun :
     (check   : Async e fs ())
  -> (finally : Async e [] ())
  -> Stream (Async e) fs ()
  -> Async e es (Fiber [] ())
parrun check = parrunCase check . const
