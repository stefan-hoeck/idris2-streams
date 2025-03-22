module FS.Core

import public Data.Linear.ELift1
import public FS.Scope

import Control.Monad.Elin

import Data.Linear.Ref1
import Data.Maybe
import Data.SortedMap

%default total

--------------------------------------------------------------------------------
-- Pull Type
--------------------------------------------------------------------------------

||| A `Pull f o es r` is a - possibly infinite - series of effectful
||| computations running in monad `f`, producing an arbitrary sequence
||| of chunks of values of type `c o` along the way, that eventually
||| terminates either with an error of type `HSum es` or with a result
||| of type `r`.
|||
||| A `Pull` is a monad with relation to `r`, so a sequencing of `Pull`s
||| via bind `(>>=)` means a sequencing of the chunks of output generated
||| a long the way. For instance, the following `Pull` will produce the
||| values `[1,2,3,4,5,6]` when being run:
|||
||| ```idris2
||| emit [1,2,3] >> emit [4,5,6]
||| ```
|||
||| A `Pull` provides capabilities for safe resource management via
||| `FS.Scope`s, allowing us to release allocated resources as soon as
|||
|||  * the pull is exhausted and produces no more output.
|||  * evaluating the pull aborts with an error.
|||  * a pull will not longer be asked to produce additional values
|||    because an outer pull has been exhaused.
|||
||| The last case occurs for instance when we stop evaluating a `Stream`
||| via `take` or `takeWhile`.
|||
||| About the effect type `f`: Most non-trivial `Pull`s and `Stream`s come
||| with the potential of failure. In addition, running a `Pull` to completion
||| requires (thread-local) mutable state to keep tracks of the evaluation
||| scopes. Effect type `f` must therefore implement interface `Data.Linear.ELift1`
||| at the very least. This still allows us to run a `Pull` or `Stream`
||| as a pure computation, for instance when using `Control.Monad.Elin`.
|||
||| Most of the time, however, we are interested in streams that produce
||| arbitrary side-effects, and an I / O monad such as `IO.Async` is required.
|||
||| A note on totality: Theoretically, we should be able define `Bind` as follows:
|||
||| ```idris
||| Bind : Pull f o es r -> Inf (r -> Pull f o es s) -> Pull f o es s
||| ```
|||
||| This would allow us to safely generate total, infinite streams of output
||| and only running a `Pull` would be a non-total function. In practice, however,
||| I found this approach to have various shortcomings: We'd need a custom
||| bind operator for defining infinite pulls. That's not hard to implement, but
||| I found it to be fairly limited and cumbersome to use, especially since
||| type inference got very erratic. For the time being, I therefore decided
||| to resort to `assert_total` when defining potentially infinite streams.
||| It's not pretty, but it gets the job done.
public export
data Pull :
       (f : List Type -> Type -> Type) -- effect type
    -> (o : Type)                      -- output type
    -> (es : List Type)                -- possible errors
    -> (r : Type)                      -- result type
    -> Type where

  ||| Constructor for producing value of type `r`
  Val    : (res : r) -> Pull f o es r

  ||| Constructor for failing with an exception
  Err    : HSum es -> Pull f o es r

  ||| Constructor for producing a chunk of output values
  Output : (val : o) -> Pull f o es ()

  ||| Wraps an arbitrary effectful computation in a `Pull`
  Exec   : (act : f es r) -> Pull f o es r

  ||| Unwraps the given child `Pull` until it either produces
  ||| a result or a chunk of output.
  Uncons : Pull f o es r -> Pull f q es (Either r (o, Pull f o es r))

  ||| Attempts to evaluate the underlying `Pull`, returning any error
  ||| wrapped in a `Left` and a successful result in a `Right`. This is
  ||| the primitive used for error handling.
  Att    : Pull f o es r -> Pull f o fs (Result es r)

  ||| Sequencing of `Pull`s via monadic bind `(>>=)`.
  Bind   : Pull f o es r -> (r -> Pull f o es t) -> Pull f o es t

  ||| Runs the given `Pull` in a new child scope. The optional second argument
  ||| is used to check, if the scope has been interrupted.
  OScope : Interrupt f -> Pull f o es r -> Pull f o es r

  ||| Safe resource management: Once the given resource has been acquired,
  ||| it is released via the given cleanup hook once the current scope ends.
  Acquire : f es r -> (r -> f [] ()) -> Pull f o es r

  ||| Internal: Evaluates the given `Pull` in the given inner scope as
  ||| long as it produces chunks of output. Switches back to the outer scope
  ||| once the `Pull` is exhausted.
  WScope : Pull f o es r -> (inner, outer : ScopeID) -> Pull f o es r

  ||| Internal: A pull for returning the current scope
  GScope : Pull f o es (Scope f)

  ||| Internal: Forces the given pull to be evaluated in the given scope.
  |||
  ||| This is used when evaluating pulls in parallel (for instance, when zipping
  ||| or merging streams): Both pulls must be run in the outer scope to prevent
  ||| the resources of the second pull to be release early when the first once
  ||| is exhausted. See `stepLeg` and `StepLeg`.
  IScope : Scope f -> Pull f o es r -> Pull f o es r

  ||| Continues with the second pull in case the first is interrupted.
  OnIntr : Pull f o es r -> Lazy (Pull f o es r) -> Pull f o es r

||| Alias for a `Pull` with a trivial return type.
public export
0 Stream : (List Type -> Type -> Type) -> List Type -> Type -> Type
Stream f es o = Pull f o es ()

||| Alias for a `Pull` that cannot produce any output.
public export
0 EmptyPull : (List Type -> Type -> Type) -> List Type -> Type -> Type
EmptyPull f = Pull f Void

||| Alias for a `Pull` that cannot produce any output.
public export
0 EmptyStream : (List Type -> Type -> Type) -> List Type -> Type
EmptyStream f es = Stream f es Void

||| A (partially evaluated) `Pull` plus the scope it should be
||| evaluated in.
public export
record StepLeg f es o where
  constructor SL
  pull  : Pull f o es ()
  scope : Scope f

--------------------------------------------------------------------------------
-- Primitives
--------------------------------------------------------------------------------

||| Lifts the given effectful computation into a `Pull`.
export %inline
exec : f es r -> Pull f o es r
exec = Exec

||| Emits a single chunk of output.
export %inline
emit : o -> Stream f es o
emit = Output

||| Returns the current evaluation scope.
|||
||| This is an internal primitive that can be used to implement
||| new combinators and topologies.
export %inline
scope : Pull f o es (Scope f)
scope = GScope

||| Creates a new scope for running the given `Pull` in
export %inline
newScope : Pull f o es r -> Pull f o es r
newScope = OScope None

||| Forces the given `Pull` to be evaluated in the given scope.
|||
||| This is an internal primitive that can be used to implement
||| new combinators and topologies.
export %inline
inScope : Scope f -> Pull f o es r -> Pull f o es r
inScope = IScope

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

||| A `Pull` is a `Functor`, `Applicative`, and `Monad`, all of which
||| follow from it implementing `MErr`, which adds capabilities for error
||| handling.
export %inline
MErr (Pull f o) where
  fail        = Err
  succeed     = Val
  bind        = Bind
  attempt     = Att
  mapImpl f p = Bind p (Val . f)
  appImpl f p = Bind f (`mapImpl` p)

||| In case the effect type of a pull has support for mutable state in
||| state thread `s`, so does the `Pull` itself.
export %inline
ELift1 s f => ELift1 s (Pull f o) where
  elift1 = Exec . elift1

export %inline
Semigroup (Stream f es o) where
  x <+> y = x >> y

export %inline
Monoid (Stream f es o) where
  neutral = pure ()

export %inline
HasIO (f es) => HasIO (Pull f o es) where
  liftIO = Exec . liftIO

--------------------------------------------------------------------------------
-- Evaluating Pulls
--------------------------------------------------------------------------------

||| Result of evaluating a single step of a `Pull f o es r`: It either ends with
||| a final result and is exhausted, or it produces a chunk of outputput and
||| a remainder, which will be evaluated next.
public export
data StepRes :
       (f  : List Type -> Type -> Type)
    -> (o  : Type)
    -> (es : List Type)
    -> (r  : Type)
    -> Type where
  ||| Stream completed successfully with a result
  Res : (ss : Scope f) -> (res : Outcome es r) -> StepRes f o es r

  ||| Stream produced some output
  Out : (ss : Scope f) -> (chunk : o) -> Pull f o es r -> StepRes f o es r

parameters {0 f      : List Type -> Type -> Type}
           {auto tgt : Target s f}
           (ref      : Ref s (ScopeST f))

  ||| A single evaluation step of a `Pull`.
  |||
  ||| Either returns the final result or the next chunk of output
  ||| paired with the remainder of the `Pull`. Fails with an error in
  ||| case of an uncaught exception
  -- Implementation note: This is a pattern match on the different
  -- data constructors of `Pull`. The `Scope` argument is the resource
  -- scope we are currently working with.
  export covering
  step : Pull f o es r -> Scope f -> f [] (StepRes f o es r)
  step p sc = do
    False <- isInterrupted sc.interrupt | True => pure (Res sc Canceled)
    case p of
      -- We got a final result, so we just return it.
      Val res    => pure (Res sc $ Succeeded res)

      -- An exception occured so we raise it in the `f` monad.
      Err x      => pure (Res sc $ Error x)

      -- The pull produced som output. We return it together with an
      -- empty continuation.
      Output val => pure $ Out sc val (pure ())

      -- We evaluate the given effect, wrapping it in a `Res` in
      -- case it succeeds.
      Exec act   => Res sc <$> raceInterrupt sc.interrupt act

      -- We step the wrapped pull. In case it produces some output,
      -- we wrap the output and continuation in a `Res . Right`. In case
      -- it is exhausted (produces an `Out res` we wrap the `res` in
      -- a `Res . Left`.
      Uncons p   =>
        step p sc >>= \case
          Res sc res     => case res of
            Succeeded r => pure (Res sc $ Succeeded $ Left r)
            Error x     => pure (Res sc $ Error x)
            Canceled    => pure (Res sc Canceled)
          Out sc chunk x => pure (Res sc $ Succeeded $ Right (chunk, x))

      -- Monadic bind: We step the wrapped pull, passing the final result
      -- to function `g`. In case of some output being emitted, we return
      -- the output and wrap the continuation again in a `Bind`. In case
      -- of interruption, we pass on the interruption.
      Bind x g   =>
        step x sc >>= \case
          Res sc o  => case o of
            Succeeded r => step (g r) sc
            Error x     => pure (Res sc $ Error x)
            Canceled    => pure (Res sc Canceled)
          Out sc v p => pure $ Out sc v (Bind p g)

      -- We try and step the wrapped pull. In case of an error, we wrap
      -- it in a `Res . Left`. In case of a final result, we return the
      -- result wrapped ina `Res . Right`. In case of more output,
      -- the output is returned and the continuation pull is again wrapped
      -- in an `Att`. This makes sure that the pull produces output until
      -- the first error or it is exhausted or interrputed.
      Att x =>
        step x sc >>= \case
          Res sc res     => case res of
            Succeeded r => pure (Res sc $ Succeeded $ Right r)
            Error x     => pure (Res sc $ Succeeded $ Left x)
            Canceled    => pure (Res sc Canceled)
          Out sc chunk x => pure (Out sc chunk (Att x))

      -- Race completion of the `deferred` value against evaluating
      -- the given pull. Currently, if the race is canceled, this
      -- is treated as the pull being interrupted.
      OnIntr p p2 =>
        step p sc >>= \case
          Out sc v q => pure (Out sc v $ OnIntr q p2)
          Res sc o   => case o of
            Succeeded v => pure $ Res sc (Succeeded v)
            Error x     => pure $ Res sc (Error x)
            Canceled    => step p2 sc

      -- Runs pull in a new child scope. The scope is setup and registered,
      -- and the result wrapped in a `WScope`.
      OScope i p =>
        openScope ref i sc >>= \sc2 =>
          step (WScope p sc2.id sc.id) sc2

      -- Acquires some resource in the current scope and adds its
      -- cleanup hook to the current scope.
      Acquire alloc cleanup => do
        Right r <- attempt {fs = []} alloc | Left x => pure $ Res sc (Error x)
        sc2     <- addHook ref sc (cleanup r)
        pure (Res sc2 $ Succeeded r)

      -- Runs the given pull `p` in scope `id`, switching back to scope `rs`
      -- once the pull is exhausted.
      WScope p id rs => do
        -- We look up scope `id` using the current scope `sc` in case it
        -- has been deleted. We only close the current scope, if `id` was
        -- found.
        (cur,closeAfterUse) <- maybe (sc,False) (,True) <$> findScope ref id

        -- We now try and step pull `p` in the scope we looked up. In case of
        -- an error, when the scope was interrupted, or when the `Pull` was done,
        -- we close `cur` (if `closeAfterUse` equals `True`).
        step p cur >>= \case
          Out scope hd tl => pure (Out scope hd $ WScope tl id rs)
          Res outScope o  => do
            nextScope <- fromMaybe outScope <$> findScope ref rs
            when closeAfterUse (close ref cur.id)
            pure $ Res nextScope o

      -- This just returns the current scope.
      GScope => pure (Res sc $ Succeeded sc)

      -- Continues running the given pull in the given scope.
      IScope sc2 p => step p sc2

  covering
  loop : EmptyPull f es r -> Scope f -> f [] (Outcome es r)
  loop p sc =
    step p sc >>= \case
      Res _ v      => pure v
      Out sc2 _ p2 => loop p2 sc2

parameters {auto mcn : MCancel f}
           {auto tgt : Target s f}

  ||| Runs a Pull to completion in the given scope, without
  ||| closing the scope. Use this when the pull was generated from
  ||| an outer scope that is still in use.
  export covering
  pullIn : Scope f -> EmptyPull f es r -> f [] (Outcome es r)
  pullIn sc p = do
    ref <- scopes
    loop ref p sc

  ||| Runs a `Pull` to completion, eventually producing
  ||| a value of type `r`.
  |||
  ||| Note: In case of an infinite stream, this will loop forever.
  |||       In order to cancel the evaluation, consider using
  |||       `Async` and racing it with a cancelation thread (for instance,
  |||       by waiting for an operating system signal).
  export covering
  pull : EmptyPull f es r -> f [] (Outcome es r)
  pull p =
    bracket newScope
      (\(sc,ref) => loop ref p sc)
      (\(sc,ref) => close ref sc.id)

  ||| Like `pull` but without the possibility of failure. Returns `neutral`
  ||| in case the stream was interrupted.
  export covering
  mpull : Monoid r => EmptyPull f [] r -> f [] r
  mpull p =
    pull p >>= \case
      Succeeded res => pure res
      Canceled      => pure neutral
      Error x impossible
