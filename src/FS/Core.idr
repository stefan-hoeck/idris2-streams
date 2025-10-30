module FS.Core

import public Data.Linear.ELift1
import public FS.Scope

import Control.Monad.Elin

import Data.Linear.Deferred
import Data.Linear.Ref1
import Data.Maybe
import Data.SortedMap
import IO.Async

%default total

-- An effectful computation that will be run when evaluating
-- a Pull
data Action :
     (f  : List Type -> Type -> Type)
  -> (es : List Type)
  -> (r  : Type)
  -> Type where
  Eval    : (act : f es r) -> Action f es r
  Acquire : f es r -> (r -> f [] ()) -> Action f es r
  Close   : Scope f -> Result es r -> Action f es r

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
||| along the way. For instance, the following `Pull` will produce the
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
||| arbitrary side-effects, and an I/O monad such as `IO.Async` is required.
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
export
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
  Cons   : (val : o) -> Inf (Pull f o es r) -> Pull f o es r

  ||| Wraps an arbitrary effectful computation in a `Pull`
  Act    : (act : Action f es r) -> Pull f o es r

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

  ||| Internal: A pull for returning the current scope
  GScope : Pull f o es (Scope f)

  ||| Internal: Forces the given pull to be evaluated in the given scope.
  |||
  ||| This is used when evaluating pulls in parallel (for instance, when zipping
  ||| or merging streams): Both pulls must be run in the outer scope to prevent
  ||| the resources of the second pull to be release early when the first once
  ||| is exhausted. See `stepLeg` and `StepLeg`.
  IScope : Scope f -> (close : Bool) -> Pull f o es r -> Pull f o es r

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
exec = Act . Eval

||| Acquires a resource that will be released once the current
||| scope is cleaned up.
export %inline
acquire : (acq : f es r) -> (release : r -> f [] ()) -> Pull f o es r
acquire acq rel = Act $ Acquire acq rel

||| Prepends the given output to a pull.
export %inline %tcinline
cons : o -> Inf (Pull f o es r) -> Pull f o es r
cons = Cons

||| Emits a single chunk of output.
export %inline
emit : o -> Stream f es o
emit v = cons v (Val ())

||| Unwraps a `pull` either returning its final result or
||| its first output together with the remainder of the pull.
export %inline
uncons : Pull f o es r -> Pull f q es (Either r (o, Pull f o es r))
uncons = Uncons

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
inScope p = IScope p False

||| Error handling primitive: Wraps a successful result in a `Right`
||| and an error in a `Left`.
export %inline
att : Pull f o es r -> Pull f o fs (Result es r)
att = Att

||| Runs the given pull in a new child scope and interrupts
||| its evaluation once the given `Deferred` is completed.
-- TODO: We should add support for a deferred result plus error
--       handling here.
export
interruptOn :
     Deferred World a
  -> Stream (Async e) es o
  -> Stream (Async e) es o
interruptOn def p = OnIntr (OScope (I def) p) (Val ())

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
  elift1 = exec . elift1

export %inline
Semigroup (Stream f es o) where
  x <+> y = x >> y

export %inline
Monoid (Stream f es o) where
  neutral = pure ()

export %inline
HasIO (f es) => HasIO (Pull f o es) where
  liftIO = exec . liftIO

--------------------------------------------------------------------------------
-- Evaluating Pulls
--------------------------------------------------------------------------------

-- The general strategy is to convert a Pull into a running computation
-- with a stack of items itentifying the tasks that have yet to be
-- finished. See also `Stack`
data Item :
     (f     : List Type -> Type -> Type)
  -> (o,p   : Type)
  -> (es,fs : List Type)
  -> (x,y   : Type)
  -> Type where
  -- the continuation of a monadic bind on the stack
  B : (x -> Pull f o es y) -> Item f o o es es x y

  -- `Att` (error handling) on the stack
  A : Item f o o es fs r (Result es r)

  -- Handling of output (`Uncons`)
  U : Item f o p es es r (Either r (o, Pull f o es r))

  -- Changing the current evaluation scope (resource management)
  -- `cl` signifies whether the current scope should be closed and
  -- its resources cleaned up.
  S : Scope f -> (cl : Bool) -> Item f o o es es x x

  -- Resumption to use if the current pull has been interrupted.
  I : Lazy (Pull f o es r) -> Item f o o es es r r

-- Call stack used to store computational steps that are yet to follow.
data Stack :
     (f     : List Type -> Type -> Type)
  -> (o     : Type)
  -> (es,fs : List Type)
  -> (x,y   : Type)
  -> Type where
  Nil  : Stack f Void es es x x
  (::) : Item f o p es fs x y -> Stack f p fs gs y z -> Stack f o es gs x z

-- Unfolding of a `Pull`, which either arrives at an effectful
-- computation (an `Action`) plus a call stack, or a final result.
data View :
     (f  : List Type -> Type -> Type)
  -> (es : List Type)
  -> (r  : Type)
  -> Type where
  VV : Scope f -> Outcome es r -> View f es r
  VA : Scope f -> Action f es x -> Stack f o es fs x y -> View f fs y

-- Result of `traceOutput`: Output (generated via the `Cons` data constructor)
-- can *only* be handled via the `Uncons` data constructor. Therefore, whenever
-- a `Cons` is encountered, the current stack is traversed until we arrive
-- at a `U` item (representing an `Uncons`), and the previously unfolded Pull
-- is reassembled during this search. The output plus reassebled pull are then
-- paired and wrapped in a `Right`.
record URes (f : List Type -> Type -> Type) (fs : List Type) (y : Type) where
  constructor UR
  {0 out, res  : Type}
  {0 errs : List Type}
  scope : Scope f
  cur   : Pull f out errs res
  stck  : Stack f out errs fs res y

-- Traverses the stack until an `Unfold` (`U` item) is encountered.
-- The stack's prefix is reassembled into a Pull that is then
-- used as the continuation together with the current output.
traceOutput :
     Scope f
  -> o
  -> Pull f o es x
  -> Stack f o es fs x y
  -> URes f fs y
traceOutput sc v p []        = UR sc p []
traceOutput sc v p (i :: is) =
  case i of
    B g       => traceOutput sc v (Bind p g) is
    A         => traceOutput sc v (Att p) is
    U         => UR sc (Val $ Right (v, p)) is
    S prev cl => traceOutput prev v (IScope sc cl p) is
    I q       => traceOutput sc v (OnIntr p q) is

parameters {0 f      : List Type -> Type -> Type}
           {auto tgt : Target s f}
           (ref      : Ref s (ScopeST f))

  -- Tail-recursively unfolds a `Pull` placing all continuations on
  -- the call stack until we either arrive at a final result or at
  -- an effectful computation (`Action`).
  covering
  view :
       Scope f
    -> Pull f o es x
    -> Stack f o es fs x y
    -> F1 s (View f fs y)
  view sc p st t =
    case p of
      Bind q g => case q of
        -- This is here for reasons of efficiency: If a `Bind` wraps
        -- a pure value, the value can be passed to the continuation
        -- directly. Otherwise, the continuation is put on the stack.
        Val v => view sc (g v) st t
        _     => view sc q (B g::st) t

      -- We arrived at a terminal (a result), at it's time to
      -- pass it to the head of the stack (if any).
      Val v => case st of
        h::tl => case h of
          -- monadic bind: we pass result `v` to continuation `fun`
          -- and continue from there
          B fun  => view sc (fun v) tl t

          -- `Uncons`: We arrived at the pull's end, so we pass
          -- the result wrapped in a `Left` (see the type of `Uncons`)
          U      => view sc (Val $ Left v) tl t

          -- error handling: there was no error so we wrap the result
          -- in a `Right`.
          A      => view sc (Val $ Right v) tl t

          -- Scope handling. In case the current scope needs to be
          -- closed, we arrived at an effectful computation and return
          -- it as our result. Otherwise, we just continue with the
          -- new scope.
          S s2 b => case b of
            True  => VA s2 (Close sc $ Right v) tl # t
            False => view s2 p tl t

          -- Interrupt handling. We were not interrupted, so we just
          -- continue.
          I _    => view sc p tl t
        []    => VV sc (Succeeded v) # t

      -- An error occured. Let's try and handle it.
      Err v => case st of
        h::tl => case h of
          -- We can't continue with the bind, so we drop it and look
          -- if there is an error handler further down the stack.
          B _    => view sc (Err v) tl t

          -- We can't continue with the `Uncons`, so we drop it and look
          -- if there is an error handler further down the stack.
          U      => view sc (Err v) tl t

          -- We found an error handler, so we wrap the error in a `Left`
          -- and continue regularily.
          A      => view sc (Val $ Left v) tl t

          -- Scope handling. In case the current scope needs to be
          -- closed, we arrived at an effectful computation and return
          -- it as our result. Otherwise, we just continue with the
          -- new scope.
          S s2 b => case b of
            True  => VA s2 (Close sc $ Left v) tl # t
            False => view s2 (Err v) tl t

          -- Interrupt handling. We were not interrupted, so we just
          -- continue.
          I _    => view sc p tl t
        []    => VV sc (Error v) # t

      -- Some output was produced. The only way this can be handled
      -- is by an `Uncons` wrapper, which by now should be on the
      -- stack. We try to find and continue from there. This will
      -- reassemble parts of the wrapping pull, so we might go
      -- back and forth on the stack for some time (until all
      -- output has been consumed, or consumption is aborted)
      Cons v q =>
       let UR sc2 p2 st2 := traceOutput sc v q st
        in view sc2 p2 st2 t

      -- An effectful computation. We have to stop here and pass control
      -- to `loop`
      Act x => VA sc x st # t

      -- We are looking for some output, so we put an uncons handler
      -- `U` on the stack.
      Uncons q => view sc q (U :: st) t

      -- Error handling. We put the corresponding item onto the stack
      -- and continue.
      Att q    => view sc q (A::st) t

      -- Pull `q` should be run in a new scope. We open a new scope
      -- and put a note on the stack that the scope should be closed
      -- when `q` is done.
      OScope i q =>
        let s2 # t := openScope ref i sc t
         in view s2 q (S sc True :: st) t

      -- Pull `q` should be run in the given scope. We put a note
      -- on the stack that the current scope `sc` should be used
      -- and `s2` closed (if `b` is `True`) once `q` is done.
      IScope s2 b q => view s2 q (S sc b :: st) t

      -- We have been asked for the current scope so we wrap it
      -- in a `Val` and continue.
      GScope   => view sc (Val sc) st t

      -- An interrupt handler should be put on the stack: `q1`
      -- will be evaluated and `q2` should be used in its stead in
      -- case it has been interrupted.
      OnIntr q1 q2 => view sc q1 (I q2 :: st) t

  -- This is invoked if evaluation of the pull has been interrupted
  -- by an external event. We look on the stack for an interrupt handler
  -- (item `I`) or - if none is found - terminate with `Canceled`.
  covering
  interrupted : Scope f -> Stack f o es fs x y -> f [] (Outcome fs y)

  -- main run loop: Keeps invoking `view`, executing the actions
  -- it gets back until a result is found or evaluation of the
  -- pull interrupted by an external event.
  covering
  loop : Scope f -> Pull f o es x -> Stack f o es fs x y -> f [] (Outcome fs y)
  loop sc p st = Prelude.do
    -- We check if the current scope has been interrupted
    -- If that'e the case, we search for an interrupt handler by
    -- passing control to `interrupted`
    False <- isInterrupted sc.interrupt | True => interrupted sc st

    -- We unfold the current pull until we either arrive at a final
    -- result or get an effectful computation we must run in order
    -- to continue
    v     <- lift1 (view sc p st)
    case v of
      VA sc2 act st2 => case act of
        -- Effect `act` should be run in monad `f`. This might
        -- be something long-running (waiting on a timer, listening
        -- on a socket) so it should be possible to interrupt this.
        -- TODO: Some (short-running) effects do not require the
        --       overhead from making them interruptible. We should
        --       consider adding a boolean flag to the `Eval` constructor.
        --       The reason this is not already there: It will complicate
        --       the API that's based on evaluating effects.
        Eval act => raceInterrupt sc.interrupt act >>= \case
          Succeeded v => loop sc2 (Val v) st2
          Error     v => loop sc2 (Err v) st2
          Canceled    => interrupted sc2 st2

        -- We should acquire a resource that should be later released
        -- See the notes above about interrupting effects.
        -- TODO: This currently does not take cancellation (of `Async`)
        --       into account and should be fixed.
        Acquire act release => raceInterrupt sc.interrupt act >>= \case
          Succeeded v => addHook ref sc2 (release v) >> loop sc2 (Val v) st2
          Error x     => loop sc2 (Err x) st2
          Canceled    => interrupted sc2 st2

        -- Scope `old` has come to an end and should be closed, thus
        -- releasing all resources that have been aqcuired within.
        Close old res => Prelude.do
          close ref True old.id
          case res of
            Right v => loop sc2 (Val v) st2
            Left  v => loop sc2 (Err v) st2

      -- We are done! Yay!
      VV sc v => pure v

  -- Implementation of `interrupted`
  interrupted sc []      = pure Canceled
  interrupted sc (h::tl) =
    case h of
      -- Of course we keep closing scopes and releasing resources!
      S sc2 True  => close ref True sc.id >> interrupted sc2 tl

      -- Nothing to do except switching to a different scope.
      S sc2 False => interrupted sc2 tl

      -- We arrived at an interrupt handler and can continue with
      -- the replacement pull `q`.
      I q         => loop sc q tl

      -- In all other cases, there is nothing to do. Note: We don't
      -- use a catch-all pattern here to make sure we don't miss any
      -- data constructors that might be introduced at a later point.
      B _         => interrupted sc tl
      U           => interrupted sc tl
      A           => interrupted sc tl

parameters {auto mcn : MCancel f}
           {auto tgt : Target s f}

  ||| Runs a Pull to completion in the given scope, without
  ||| closing the scope. Use this when the pull was generated from
  ||| an outer scope that is still in use.
  export covering
  pullIn : Scope f -> Pull f Void es r -> f [] (Outcome es r)
  pullIn sc p = do
    ref <- scopes
    loop ref sc p []

  ||| Runs a `Pull` to completion, eventually producing
  ||| a value of type `r`.
  |||
  ||| Note: In case of an infinite stream, this will loop forever.
  |||       In order to cancel the evaluation, consider using
  |||       `Async` and racing it with a cancelation thread (for instance,
  |||       by waiting for an operating system signal).
  export covering
  pull : Pull f Void es r -> f [] (Outcome es r)
  pull p =
    bracket newScope
      (\(sc,ref) => loop ref sc p [])
      (\(sc,ref) => close ref False sc.id)

  ||| Like `pull` but without the possibility of failure. Returns `neutral`
  ||| in case the stream was interrupted.
  export covering
  mpull : Monoid r => Pull f Void [] r -> f [] r
  mpull p =
    pull p >>= \case
      Succeeded res => pure res
      Canceled      => pure neutral
      Error x impossible
