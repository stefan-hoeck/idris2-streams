module FS.Pull

import public Data.Linear.ELift1
import public FS.Scope

import Control.Monad.Elin

import Data.Linear.Ref1
import Data.Maybe
import Data.Nat
import Data.SortedMap


import IO.Async

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
-- Creating Pulls
--------------------------------------------------------------------------------

public export
data UnfoldRes : (r,s,o : Type) -> Type where
  More : (vals : o) -> (st : s) -> UnfoldRes r s o
  Done : (res : r) ->  UnfoldRes r s o
  Last : (res : r) ->  (vals : o) -> UnfoldRes r s o

export %inline
exec : f es r -> Pull f o es r
exec = Exec

||| Emits a single chunk of output
export %inline
emit : o -> Stream f es o
emit = Output

||| Emits a list of chunks.
export %inline
emits : List o -> Stream f es o
emits []     = pure ()
emits (h::t) = emit h >> emits t

||| Emits a single chunk of output generated from an effectful
||| computation.
export %inline
eval : f es o -> Stream f es o
eval act = Exec act >>= emit

||| Like `unfold` but emits values in larger chunks.
|||
||| This allows us to potentially emit a bunch of values right before
||| we are done.
export
unfold : (init : s) -> (s -> UnfoldRes r s o) -> Pull f o es r
unfold init g =
  assert_total $ case g init of
    More vals st => emit vals >> unfold st g
    Done res      => pure res
    Last res vals => emit vals $> res

||| Like `unfold` but produces values via an effectful computation
||| until a `Done` or `Last` is returned.
export
unfoldEval : (init : s) -> (s -> f es (UnfoldRes r s o)) -> Pull f o es r
unfoldEval cur act =
  assert_total $ Exec (act cur) >>= \case
    More vals st => emit vals >> unfoldEval st act
    Done res      => pure res
    Last res vals => emit vals $> res

||| Like `unfold` but produces values via an effectful computation
||| until a `Nothing` is returned.
export
unfoldEvalMaybe : f es (Maybe o) -> Pull f o es ()
unfoldEvalMaybe act =
  assert_total $ Exec act >>= \case
    Nothing => pure ()
    Just o  => emit o >> unfoldEvalMaybe act

||| Infinitely produces chunks of values of the given size
export
fillC : o -> Pull f o es ()
fillC v = assert_total $ emit v >> fillC v

||| An infinite stream of values of type `o` where
||| the next value is built from the previous one by
||| applying the given function.
export
iterateC : o -> (o -> o) -> Stream f es o
iterateC v f = unfold v (\x => More x $ f x)

||| Infinitely cycles through the given `Pull`
export
repeat : Stream f es o -> Stream f es o
repeat v = assert_total $ v >> repeat v

||| Produces the given chunk of value `n` times.
export
replicateC : Nat -> o -> Stream f es o
replicateC 0     _ = pure ()
replicateC (S k) v = emit v >> replicateC k v

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

||| Result of breaking a value into two pieces.
public export
data BreakRes : Type -> Type where
  Broken : (pre, post : c) -> BreakRes c
  NoPre  : (post : c) -> BreakRes c
  NoPost : (pre  : c) -> BreakRes c
  None   : BreakRes c

||| Prepends the given output to pull.
export %inline
cons : o -> Pull f o es r -> Pull f o es r
cons vs p = Output vs >> p

||| Splits the first chunk of values from the head of a `Pull`, returning
||| either the final result or a list of values plus the remainder of the
||| `Pull`.
|||
||| Please note that the resulting pull will not produce any output.
export %inline
uncons : Pull f o es r -> Pull f q es (Either r (o, Pull f o es r))
uncons = Uncons

||| Emits only the first `n` chunks of values of a `Stream`.
-- TODO: Fix and check scoping
export
takeC : Nat -> Stream f es o -> Stream f es o
takeC 0     _ = pure ()
takeC (S k) p =
  uncons p >>= \case
    Left _      => pure ()
    Right (v,q) => emit v >> takeC k q

||| Discards the first `n` values of a `Stream`, returning the
||| remainder.
export
dropC : Nat -> Pull f o es r -> Pull f o es r
dropC 0     p = p
dropC (S k) p =
  uncons p >>= \case
    Left v      => pure v
    Right (v,q) => dropC k q

||| Only keeps the first element of the input.
export %inline
headC : Stream f es o -> Stream f es o
headC = takeC 1

||| Drops the first element of the input.
export %inline
tailC : Stream f es o -> Stream f es o
tailC = dropC 1

||| Like `uncons` but does not consume the chunk
export
peekC : Pull f o es r -> Pull f q es (Either r (o, Pull f o es r))
peekC p =
  uncons p >>= \case
    Left v       => pure (Left v)
    Right (vs,q) => pure $ Right (vs, cons vs q)

||| Tries to break up values until the given function returns a `Broke`.
export
breakPull : (o -> BreakRes o) -> Pull f o es r -> Pull f o es (Pull f o es r)
breakPull g p =
  assert_total $ uncons p >>= \case
    Left res    => pure (pure res)
    Right (v,q) => case g v of
      Broken pre post => emit pre $> cons post q
      NoPre post      => pure (cons post q)
      NoPost pre      => emit pre $> q
      None            => emit v >> breakPull g q

-- TODO: Adjust and check scoping
takeWhile_ : (takeFail : Bool) -> (o -> Bool) -> Stream f es o -> Stream f es o
takeWhile_ tf pred p =
  assert_total $ uncons p >>= \case
    Left v      => pure ()
    Right (o,p) => case pred o of
      True  => emit o >> takeWhile_ tf pred p
      False => case tf of
        True  => emit o
        False => pure ()

||| Emits values until the given predicate returns `False`,
||| returning the remainder of the `Pull`.
export %inline
takeWhileC : (o -> Bool) -> Stream f es o -> Stream f es o
takeWhileC = takeWhile_ False

||| Like `takeWhile` but also includes the first failure.
export %inline
takeThroughC : (o -> Bool) -> Stream f es o -> Stream f es o
takeThroughC = takeWhile_ True

||| Emits values until the given pull emits a `Nothing`.
export
takeWhileJust : Stream f es (Maybe o) -> Stream f es o
takeWhileJust p =
  assert_total $ uncons p >>= \case
    Left _      => pure ()
    Right (Just v,q)  => emit v >> takeWhileJust q
    Right (Nothing,q) => pure ()

dropWhile_ : (dropFail : Bool) -> (o -> Bool) -> Pull f o es r -> Pull f o es r
dropWhile_ df pred p =
  assert_total $ uncons p >>= \case
    Left v      => pure v
    Right (o,q) => case pred o of
      True => dropWhile_ df pred q
      False => case df of
        True  => q
        False => cons o q

||| Drops values from a stream while the given predicate returns `True`,
||| returning the remainder of the stream (if any).
export %inline
dropWhileC : (o -> Bool) -> Pull f o es r -> Pull f o es r
dropWhileC = dropWhile_ False

||| Like `dropWhile` but also drops the first value where
||| the predicate returns `False`.
export %inline
dropThroughC : (o -> Bool) -> Pull f o es r -> Pull f o es r
dropThroughC = dropWhile_ True

||| Filters the emit of a `Pull` emitting only the
||| values that fulfill the given predicate
export
mapMaybeC : (o -> Maybe p) -> Pull f o es r -> Pull f p es r
mapMaybeC f p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (v,q) => case f v of
      Just w  => emit w >> mapMaybeC f q
      Nothing => mapMaybeC f q

||| Chunk-wise maps the emit of a `Pull`
export %inline
mapC : (o -> p) -> Pull f o es r -> Pull f p es r
mapC f = mapMaybeC (Just . f)

||| Chunk-wise effectful mapping of the emit of a `Pull`
export
evalMap : (o -> f es p) -> Pull f o es r -> Pull f p es r
evalMap f p =
  assert_total $ uncons p >>= \case
    Left x       => pure x
    Right (vs,p) => do
      ws <- exec (f vs)
      emit ws
      evalMap f p

||| Chunk-wise effectful mapping of the emit of a `Pull`
export
evalMapMaybe : (o -> f es (Maybe p)) -> Pull f o es r -> Pull f p es r
evalMapMaybe f p =
  assert_total $ uncons p >>= \case
    Left x       => pure x
    Right (v,q) => do
      Just w <- exec (f v) | Nothing => evalMapMaybe f q
      emit w
      evalMapMaybe f q

||| Filters the emit of a `Pull` emitting only the
||| values that fulfill the given predicate
export
filter : (o -> Bool) -> Pull f o es r -> Pull f o es r
filter pred p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (v,q) => case pred v of
      True  => emit v >> filter pred q
      False => filter pred q

||| Wraps the values emitted by this stream in a `Just` and
||| marks its end with a `Nothing`.
export
endWithNothing : Pull f o es r -> Pull f (Maybe o) es r
endWithNothing s = mapC Just s >>= \res => emit Nothing $> res

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

||| Folds the emit of a pull using an initial value and binary operator.
export
pfoldC : (p -> o -> p) -> p -> Pull f o es r -> Pull f q es (p,r)
pfoldC g v s =
  assert_total $ uncons s >>= \case
    Left res      => pure (v,res)
    Right (vs,s2) => pfoldC g (g v vs) s2

||| Folds all input using an initial value and binary operator
export %inline
foldC : (p -> o -> p) -> p -> Stream f es o -> Pull f q es p
foldC f v = map fst . pfoldC f v

||| Returns `True` if all emitted values of the given stream fulfill
||| the given predicate
export
allC : (o -> Bool) -> Stream f es o -> Pull f q es Bool
allC pred p =
  assert_total $ uncons p >>= \case
    Left _ => pure True
    Right (vs,q) => case pred vs of
      True  => allC pred q
      False => pure False

||| Returns `True` if any of the emitted values of the given stream fulfills
||| the given predicate
export
anyC : (o -> Bool) -> Pull f o es () -> Pull f q es Bool
anyC pred p =
  assert_total $ uncons p >>= \case
    Left _ => pure False
    Right (vs,q) => case pred vs of
      False  => anyC pred q
      True   => pure True

export %inline
sumC : Num o => Stream f es o -> Pull f q es o
sumC = foldC (+) 0

export %inline
countC : Stream f es o -> Pull f q es Nat
countC = foldC (const . S) 0

||| General stateful conversion of a `Pull`s emit.
|||
||| Aborts as soon as the given accumulator function returns `Nothing`
export
scanMaybe : s -> (s -> Maybe (o -> (p,s))) -> Stream f es o -> Pull f p es s
scanMaybe s1 f p =
  assert_total $ case f s1 of
    Nothing => pure s1
    Just g  => uncons p >>= \case
      Left _      => pure s1
      Right (v,p) => let (w,s2) := g v in emit w >> scanMaybe s2 f p

||| Like `scanMaybe` but will transform the whole emit.
export %inline
scan : s -> (s -> o -> (p,s)) -> Stream f es o -> Pull f p es s
scan s1 f = scanMaybe s1 (Just . f)

||| Like `scan` but will possibly also emit the final state.
export
scanFull :
     s
  -> (s -> o -> (p,s))
  -> (s -> Maybe p)
  -> Stream f es o
  -> Stream f es p
scanFull s1 f last p = do
  v <- scan s1 f p
  case last v of
    Just rem => emit rem
    Nothing  => pure ()

--------------------------------------------------------------------------------
-- Resource Management
--------------------------------------------------------------------------------

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

||| Acquires a resource that will be released once the current
||| scope is cleaned up.
export %inline
acquire : (acq : f es r) -> (release : r -> f [] ()) -> Pull f o es r
acquire = Acquire

||| Like `bracket`, but acquires the resource in the current scope.
export
bracketWeak : (f es x) -> (x -> f [] ()) -> (x -> Pull f o es r) -> Pull f o es r
bracketWeak acq cleanup g = acquire acq cleanup >>= g

||| Acquires a resource used for running a stream
||| making sure it is properly cleaned up once the stream terminates.
export %inline
bracket : (f es x) -> (x -> f [] ()) -> (x -> Pull f o es r) -> Pull f o es r
bracket acq cl = newScope . bracketWeak acq cl

||| Makes sure the given cleanup action is run once the stream
||| terminates.
|||
||| Like `finally` but does not create a new inner scope.
export
finallyWeak : Applicative (f es) => f [] () -> Pull f o es r -> Pull f o es r
finallyWeak cleanup = bracketWeak (pure ()) (const cleanup) . const

||| Makes sure the given cleanup action is run once the stream
||| terminates.
export
finally : Applicative (f es) => f [] () -> Pull f o es r -> Pull f o es r
finally cleanup = bracket (pure ()) (const cleanup) . const

||| Like `resource`, but acquires the resource in the current scope.
export %inline
resourceWeak :
     {auto res : Resource f x}
  -> (acquire : f es x)
  -> (x -> Pull f o es r)
  -> Pull f o es r
resourceWeak acq = bracketWeak acq cleanup

||| Acquires a resource in a new scope, closing it once the scope is
||| cleaned up.
export %inline
resource :
     {auto res : Resource f x}
  -> (acquire : f es x)
  -> (x -> Pull f o es r)
  -> Pull f o es r
resource acq = bracket acq cleanup

export
resourcesWeak :
     {auto all : All (Resource f) rs}
  -> (acquire : All (f es) rs)
  -> (HList rs -> Pull f o es r)
  -> Pull f o es r
resourcesWeak @{_ :: _} (a::as) g =
  resourceWeak a $ \r => resourcesWeak as (\res => g (r::res))
resourcesWeak @{[]} [] g = g []

export
resources :
     {auto all : All (Resource f) rs}
  -> (acquire : All (f es) rs)
  -> (HList rs -> Pull f o es r)
  -> Pull f o es r
resources acqs = newScope . resourcesWeak acqs

||| Like `uncons`, but pairs the tail of the `Pull` with the `Scope`
||| it should be run in.
|||
||| Use this for evaluating several `Pull`s in parallel, for instance
||| when zipping or merging them. This will make sure that all resources
||| will be released in the correct order.
export
stepLeg : StepLeg f es o -> Pull f q es (Maybe (o, StepLeg f es o))
stepLeg (SL p sc) =
  inScope sc $ do
    uncons p >>= \case
      Left _       => pure Nothing
      Right (v,tl) => (\sc => Just (v, SL tl sc)) <$> scope

||| Utility for consing some values onto a pull and running it in
||| its desired scope.
export
endLeg : o -> StepLeg f es o -> Pull f o es ()
endLeg vs (SL p sc) = inScope sc (cons vs p)

--------------------------------------------------------------------------------
-- Observing and Draining Streams
--------------------------------------------------------------------------------

||| Performs the given action on each emitted chunk of values, thus draining
||| the stream, consuming all its output.
|||
||| For acting on output without actually draining the stream, see
||| `observe` and `observe1`.
export
foreach : (o -> f es ()) -> Pull f o es r -> Pull f q es r
foreach f p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (v,p) => exec (f v) >> foreach f p

||| Empties a stream silently dropping all output.
export
drain : Pull f o es r -> Pull f q es r
drain p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (_,p) => drain p

||| Performs the given action on every chunk of values of the stream without
||| otherwise affecting the emitted values.
export
observe : (o -> f es ()) -> Pull f o es r -> Pull f o es r
observe act p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (v,p) => exec (act v) >> cons v (observe act p)

export
unconsBind : Pull f o es r -> (o -> Pull f p es ()) -> Pull f p es r
unconsBind p g =
  assert_total $ uncons p >>= \case
    Left v       => pure v
    Right (os,q) => g os >> unconsBind q g

||| Flipped version of `unconsBind`
export %inline
bindC : (o -> Pull f p es ()) -> Pull f o es r -> Pull f p es r
bindC = flip unconsBind

export
attemptC : Pull f o es () -> Pull f (Result es o) fs ()
attemptC p =
  Att (mapC Right p) >>= \case
    Left x  => emit (Left x)
    Right _ => pure ()

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
