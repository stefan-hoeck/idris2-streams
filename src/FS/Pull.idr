module FS.Pull

import public Data.Linear.ELift1
import public FS.Scope

import Control.Monad.Elin
import Control.Monad.Identity

import Data.Linear.Ref1
import Data.List1
import Data.Maybe
import Data.Nat
import Data.SortedMap

import FS.Chunk

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
||| output [1,2,3] >> output [4,5,6]
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
  Eval   : (act : f es r) -> Pull f o es r

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

||| Alias for a `Pull` operating on lists of values.
public export
0 PullN : (List Type -> Type -> Type) -> Type -> List Type -> Type -> Type
PullN f o = Pull f (List1 o)

||| Alias for a `Pull` that emits single values.
public export
0 Pull1 : (List Type -> Type -> Type) -> Type -> List Type -> Type -> Type
Pull1 f o = Pull f (Identity o)

||| Alias for a `Pull` that cannot produce any output.
public export
0 EmptyPull : (List Type -> Type -> Type) -> List Type -> Type -> Type
EmptyPull f = Pull1 f Void

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
  elift1 = Eval . elift1

--------------------------------------------------------------------------------
-- Creating Pulls
--------------------------------------------------------------------------------

||| Emits a single value of output
export %inline
output : o -> Pull f o es ()
output = Output

||| Like `unfold` but emits values in larger chunks.
|||
||| This allows us to potentially emit a bunch of values right before
||| we are done.
export
unfold : (init : s) -> (s -> UnfoldRes r s o) -> Pull f o es r
unfold init g =
  assert_total $ case g init of
    Chunk vals st => output vals >> unfold st g
    Done res      => pure res
    Last res vals => output vals $> res

||| Like `unfold` but produces values via an effectful computation
||| until a `Done` or `Last` is returned.
export
unfoldEval : (init : s) -> (s -> f es (UnfoldRes r s o)) -> Pull f o es r
unfoldEval cur act =
  assert_total $ Eval (act cur) >>= \case
    Chunk vals st => output vals >> unfoldEval st act
    Done res      => pure res
    Last res vals => output vals $> res

||| Like `unfold` but produces values via an effectful computation
||| until a `Nothing` is returned.
export
unfoldEvalMaybe : f es (Maybe o) -> Pull f o es ()
unfoldEvalMaybe act =
  assert_total $ Eval act >>= \case
    Nothing => pure ()
    Just o  => output o >> unfoldEvalMaybe act

||| Emits values until the given generator function returns a `Left`
export %inline
unfold1 : ChunkSize => Unfold c o => s -> (s -> Either r (o,s)) -> Pull f c es r
unfold1 init g = unfold init (unfoldImpl g)

||| Infinitely produces chunks of values of the given size
export
fill : ChunkSize => Unfold c o => o -> Pull f c es ()
fill v =
  let chunk := unfoldImpl (\_ => Right (v,())) ()
   in unfold () (const chunk)

||| An infinite stream of values of type `o` where
||| the next value is built from the previous one by
||| applying the given function.
export
iterate : ChunkSize => Unfold c o => o -> (o -> o) -> Pull f c es ()
iterate v f = unfold1 v (\x => Right (x, f x))

||| Infinitely cycles through the given `Pull`
export
repeat : Pull f o es () -> Pull f o es ()
repeat v = assert_total $ v >> repeat v

||| Produces the given value `n` times as chunks of the given size.
export
replicate : ChunkSize => Unfold c o => Nat -> o -> Pull f c es ()
replicate n v =
  unfold1 n $ \case
    0   => Left ()
    S k => Right (v,k)

||| Returns the current evaluation scope.
|||
||| This is an internal primitive that can be used to implement
||| new combinators and topologies.
export %inline
scope : Pull f o es (Scope f)
scope = GScope

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

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

export %inline
cons : o -> Pull f o es r -> Pull f o es r
cons vs p = Output vs >> p

export %inline
consMaybe : Maybe o -> Pull f o es r -> Pull f o es r
consMaybe (Just vs) p = cons vs p
consMaybe Nothing   p = p

||| Splits the first chunk of values from the head of a `Pull`, returning
||| either the final result or a list of values plus the remainder of the
||| `Pull`.
|||
||| Please note that the resulting pull with not produce any output.
export %inline
uncons : Pull f o es r -> Pull f q es (Either r (o, Pull f o es r))
uncons = Uncons

||| Splits the very value from the head of a `Pull`
export
uncons1 : Uncons c o => Pull f c es r -> Pull f q es (Either r (o, Pull f c es r))
uncons1 p =
  assert_total $ uncons p >>= \case
    Left x => pure (Left x)
    Right (vs,q) =>
      let (v,m) := unconsImpl vs
       in pure (Right (v,consMaybe m q))

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

||| Emits the first `n` values of a `Pull`, returning the
||| remainder.
export
take : Split o => Nat -> Pull f o es r -> Pull f o es (Pull f o es r)
take k p =
  assert_total $ uncons p >>= \case
    Left v      => pure (pure v)
    Right (vs,q) => case splitAt k vs of
      Middle pre post => output pre $> cons post q
      All pre n       => output pre >> take n q
      Naught          => pure (cons vs q)

||| Drops the first `n` values of a `Pull`, returning the
||| remainder.
export
drop : Split o => Nat -> Pull f o es r -> Pull f o es r
drop k p =
  assert_total $ uncons p >>= \case
    Left v      => pure v
    Right (vs,q) => case splitAt k vs of
      Middle pre post => cons post q
      All _ n         => drop n q
      Naught          => q

||| Like `uncons` but does not consume the chunk
export
peek : Pull f o es r -> Pull f q es (Either r (o, Pull f o es r))
peek p =
  uncons p >>= \case
    Left v       => pure (Left v)
    Right (vs,q) => pure $ Right (vs, cons vs q)


export
break : Break c o => (o -> Bool) -> Pull f c es r -> Pull f c es (Pull f c es r)
break pred p =
  assert_total $ uncons p >>= \case
    Left res     => pure (pure res)
    Right (vs,q) => case breakImpl pred vs of
      Broke xs ys => output xs $> cons ys q
      First       => pure (cons vs q)
      None        => output vs >> break pred q

-- takeWhile_ :
--      (takeFailure : Bool)
--   -> (o -> Bool)
--   -> Pull f o es r
--   -> Pull f o es (Maybe $ Pull f o es r)
-- takeWhile_ tf pred p =
--   assert_total $ uncons p >>= \case
--     Left _      => pure Nothing
--     Right (o,p) => case takeWhileImpl tf [<] pred o of
--       Nothing    => cons o $ takeWhile_ tf pred p
--       Just (l,r) => output l $> Just (cons r p)
--
-- ||| Emits values until the given predicate returns `False`,
-- ||| returning the remainder of the `Pull`.
-- export %inline
-- takeWhile :
--      (o -> Bool)
--   -> Pull f o es r
--   -> Pull f o es (Maybe $ Pull f o es r)
-- takeWhile = takeWhile_ False
--
-- ||| Like `takeWhile` but also includes the first failure.
-- export %inline
-- takeThrough :
--      (o -> Bool)
--   -> Pull f o es r
--   -> Pull f o es (Maybe $ Pull f o es r)
-- takeThrough = takeWhile_ True
--
-- ||| Emits values until the given pull emits a `Nothing`.
-- export
-- takeWhileJust :
--      Pull f (Maybe o) es r
--   -> Pull f o es (Pull f (Maybe o) es r)
-- takeWhileJust p =
--   assert_total $ uncons p >>= \case
--     Left v      => pure (pure v)
--     Right (o,p) => case takeWhileJustImpl [<] o of
--       (l,[]) => cons l $ takeWhileJust p
--       (l,r)  => output l $> cons r p
--
-- ||| Emits the last `n` elements of the input
-- |||
-- ||| Note: The whole `n` values have to be kept in memory, therefore,
-- |||       the result will be emitted as a single chunk. Take memory
-- |||       consumption into account when using this for very large `n`.
-- export
-- takeRight :
--      (n : Nat)
--   -> {auto 0 p : IsSucc n}
--   -> Pull f o es ()
--   -> Pull f q es (List o)
-- takeRight n = go []
--   where
--     go : List o -> Pull f o es () -> Pull f q es (List o)
--     go xs p =
--       assert_total $ unconsN n True p >>= \case
--         Nothing     => pure xs
--         Just (ys,q) => go (drop (length ys) xs ++ ys) q
--
-- dropWhile_ :
--      (dropFailure : Bool)
--   -> (o -> Bool)
--   -> Pull f o es ()
--   -> Pull f o es (Maybe $ Pull f o es ())
-- dropWhile_ df pred p =
--   assert_total $ uncons p >>= \case
--     Left _      => pure Nothing
--     Right (o,p) => case dropWhileImpl pred o of
--       []   => dropWhile_ df pred p
--       h::t => case df of
--         True  => pure $ Just (cons t p)
--         False => pure $ Just (Output (h::t) >> p)
--
-- ||| Drops values from a stream while the given predicate returns `True`,
-- ||| returning the remainder of the stream (if any).
-- export
-- dropWhile :
--      (o -> Bool)
--   -> Pull f o es ()
--   -> Pull f o es (Maybe $ Pull f o es ())
-- dropWhile = dropWhile_ False
--
-- ||| Like `dropWhile` but also drops the first value where
-- ||| the predicate returns `False`.
-- export
-- dropThrough :
--      (o -> Bool)
--   -> Pull f o es ()
--   -> Pull f o es (Maybe $ Pull f o es ())
-- dropThrough = dropWhile_ True
--
-- ||| Returns the first value fulfilling the given predicate
-- ||| together with the remainder of the stream.
-- export
-- find :
--      (o -> Bool)
--   -> Pull f o es ()
--   -> Pull f p es (Maybe (o, Pull f o es ()))
-- find pred p =
--   assert_total $ uncons p >>= \case
--     Left _       => pure Nothing
--     Right (os,q) => case findImpl pred os of
--       Just (v,rem) => pure (Just (v, cons rem q))
--       Nothing      => find pred q
--
-- ||| Chunk-wise maps the output of a `Pull`
-- export %inline
-- mapChunk : (c o -> d p) -> Pull f o es r -> Pull d f p es r
-- mapChunk f p =
--   assert_total $ uncons p >>= \case
--     Left x       => pure x
--     Right (vs,p) => consChunk (f vs) $ mapChunk f p
--
-- ||| Chunk-wise effectful mapping of the output of a `Pull`
-- export
-- mapChunkEval : (c o -> f es (d p)) -> Pull f o es r -> Pull d f p es r
-- mapChunkEval f p =
--   assert_total $ uncons p >>= \case
--     Left x       => pure x
--     Right (vs,p) => do
--       ws <- Eval (f vs)
--       consChunk ws $ mapChunkEval f p
--
-- ||| Consumes the produced chunks of output, draining the pull.
-- export
-- sinkChunk : (c o -> f es ()) -> Pull f o es r -> Pull d f p es r
-- sinkChunk f p =
--   assert_total $ uncons p >>= \case
--     Left x       => pure x
--     Right (vs,p) => Eval (f vs) >> sinkChunk f p
--
-- ||| Consumes the produced output, draining the pull.
-- |||
-- ||| See also `sinkChunk` for a potentially more efficient version.
-- export
-- sink : (o -> f es ()) -> Pull f o es r -> Pull f p es r
-- sink f p =
--   assert_total $ uncons1 p >>= \case
--     Left x      => pure x
--     Right (v,p) => Eval (f v) >> sink f p
--
-- ||| Consumes the produced chunks of output without draining the pull.
-- export
-- observeOutput : (c o -> f es ()) -> Pull f o es r -> Pull f o es r
-- observeOutput f p =
--   assert_total $ uncons p >>= \case
--     Left x       => pure x
--     Right (vs,p) => Eval (f vs) >> outputChunk vs >> observeOutput f p
--
-- ||| Maps the output of a `Pull`
-- export %inline
-- mapOutput : (o -> p) -> Pull f o es r -> Pull f p es r
-- mapOutput = mapChunk . map
--
-- ||| Filters the output of a `Pull` emitting only the
-- ||| values that fulfill the given predicate
-- export %inline
-- filter : (o -> Bool) -> Pull f o es r -> Pull f o es r
-- filter = mapChunk . filter
--
-- ||| Folds all input chunk-wise using an initial value and
-- ||| binary operator
-- export
-- foldChunk : p -> (p -> c o -> p) -> Pull f o es () -> Pull d f q es p
-- foldChunk v g s =
--   assert_total $ uncons s >>= \case
--     Left _        => pure v
--     Right (vs,s2) => foldChunk (g v vs) g s2
--
-- ||| Folds all input using an initial value and binary operator
-- export %inline
-- fold : p -> (p -> o -> p) -> Pull f o es () -> Pull f q es p
-- fold v = foldChunk v . foldl
--
-- ||| Folds all input using the supplied binary operator.
-- |||
-- ||| This returns `Nothing` in case the stream does not produce any
-- ||| values.
-- export %inline
-- fold1 : (o -> o -> o) -> Pull f o es () -> Pull f q es (Maybe o)
-- fold1 g p =
--   assert_total $ uncons p >>= \case
--     Left _         => pure Nothing
--     Right (h::t,q) => Just <$> fold (foldl g h t) g q
--     Right ([],q)   => fold1 g q
--
-- ||| Returns `True` if all emitted values of the given stream fulfill
-- ||| the given predicate
-- export
-- all : (o -> Bool) -> Pull f o es () -> Pull f q es Bool
-- all pred p =
--   assert_total $ uncons p >>= \case
--     Left _ => pure True
--     Right (vs,q) => case all pred vs of
--       True  => all pred q
--       False => pure False
--
-- ||| Returns `True` if any of the emitted values of the given stream fulfills
-- ||| the given predicate
-- export
-- any : (o -> Bool) -> Pull f o es () -> Pull f q es Bool
-- any pred p =
--   assert_total $ uncons p >>= \case
--     Left _ => pure False
--     Right (vs,q) => case any pred vs of
--       False  => any pred q
--       True   => pure True
--
-- ||| General stateful conversion of a `Pull`s output.
-- |||
-- ||| Aborts as soon as the given accumulator function returns `Nothing`
-- export
-- scanChunkMaybe :
--      x
--   -> (x -> Maybe (c o -> (d p,x)))
--   -> Pull f o es ()
--   -> Pull d f p es x
-- scanChunkMaybe s1 f p =
--   assert_total $ case f s1 of
--     Nothing => pure s1
--     Just g  => uncons p >>= \case
--       Left r      => pure s1
--       Right (v,p) => let (w,s2) := g v in consChunk w $ scanChunkMaybe s2 f p
--
-- ||| Like `scanChunkMaybe` but will transform the whole output.
-- export
-- scanChunk : x -> (x -> c o -> (d p,x)) -> Pull f o es () -> Pull d f p es x
-- scanChunk s1 f = scanChunkMaybe s1 (Just . f)

export
unconsBind : Pull f o es r -> (o -> Pull f p es ()) -> Pull f p es r
unconsBind p g =
  assert_total $ uncons p >>= \case
    Left v       => pure v
    Right (os,q) => g os >> unconsBind q g

||| Flipped version of `unconsBind`
export %inline
bindOutput : (o -> Pull f p es ()) -> Pull f o es r -> Pull f p es r
bindOutput = flip unconsBind

-- export
-- bindOutput1 : (o -> Pull f p es ()) -> Pull f o es () -> Pull f p es ()
-- bindOutput1 f p =
--   assert_total $ uncons1 p >>= \case
--     Left _      => pure ()
--     Right (v,q) => f v >> bindOutput1 f q
--
-- export
-- attemptOutput1 : Pull1 f o es () -> Pull1 f (Result es o) fs ()
-- attemptOutput1 p =
--   Att (mapChunk Right p) >>= \case
--     Left x  => outputChunk (Left x)
--     Right _ => pure ()
--
-- export
-- attemptOutput : Pull f o es () -> Pull f (Result es o) fs ()
-- attemptOutput p =
--   Att (mapOutput Right p) >>= \case
--     Left x  => output1 (Left x)
--     Right _ => pure ()
--
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
  Done : (ss : Scope f) -> (res : Outcome es r) -> StepRes f o es r

  ||| Stream produced some output
  Out  : (ss : Scope f) -> (chunk : o) -> Pull f o es r -> StepRes f o es r

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
    False <- isInterrupted sc.interrupt | True => pure (Done sc Canceled)
    case p of
      -- We got a final result, so we just return it.
      Val res    => pure (Done sc $ Succeeded res)

      -- An exception occured so we raise it in the `f` monad.
      Err x      => pure (Done sc $ Error x)

      -- The pull produced som output. We return it together with an
      -- empty continuation.
      Output val => pure $ Out sc val (pure ())

      -- We evaluate the given effect, wrapping it in a `Done` in
      -- case it succeeds.
      Eval act   => Done sc <$> raceInterrupt sc.interrupt act

      -- We step the wrapped pull. In case it produces some output,
      -- we wrap the output and continuation in a `Done . Right`. In case
      -- it is exhausted (produces an `Out res` we wrap the `res` in
      -- a `Done . Left`.
      Uncons p   =>
        step p sc >>= \case
          Done sc res     => case res of
            Succeeded r => pure (Done sc $ Succeeded $ Left r)
            Error x     => pure (Done sc $ Error x)
            Canceled    => pure (Done sc Canceled)
          Out  sc chunk x => pure (Done sc $ Succeeded $ Right (chunk, x))

      -- Monadic bind: We step the wrapped pull, passing the final result
      -- to function `g`. In case of some output being emitted, we return
      -- the output and wrap the continuation again in a `Bind`. In case
      -- of interruption, we pass on the interruption.
      Bind x g   =>
        step x sc >>= \case
          Done sc o  => case o of
            Succeeded r => step (g r) sc
            Error x     => pure (Done sc $ Error x)
            Canceled    => pure (Done sc Canceled)
          Out sc v p => pure $ Out sc v (Bind p g)

      -- We try and step the wrapped pull. In case of an error, we wrap
      -- it in a `Done . Left`. In case of a final result, we return the
      -- result wrapped ina `Done . Right`. In case of more output,
      -- the output is returned and the continuation pull is again wrapped
      -- in an `Att`. This makes sure that the pull produces output until
      -- the first error or it is exhausted or interrputed.
      Att x =>
        step x sc >>= \case
          Done sc res     => case res of
            Succeeded r => pure (Done sc $ Succeeded $ Right r)
            Error x     => pure (Done sc $ Succeeded $ Left x)
            Canceled    => pure (Done sc Canceled)
          Out  sc chunk x => pure (Out sc chunk (Att x))

      -- Race completion of the `deferred` value against evaluating
      -- the given pull. Currently, if the race is canceled, this
      -- is treated as the pull being interrupted.
      OnIntr p p2 =>
        step p sc >>= \case
          Out sc v q => pure (Out sc v $ OnIntr q p2)
          Done sc o  => case o of
            Succeeded v => pure $ Done sc (Succeeded v)
            Error x     => pure $ Done sc (Error x)
            Canceled    => step p2 sc

      -- Runs pull in a new child scope. The scope is setup and registered,
      -- and the result wrapped in a `WScope`.
      OScope i p =>
        openScope ref i sc >>= \sc2 =>
          step (WScope p sc2.id sc.id) sc2

      -- Acquires some resource in the current scope and adds its
      -- cleanup hook to the current scope.
      Acquire alloc cleanup => do
        Right r <- attempt {fs = []} alloc | Left x => pure $ Done sc (Error x)
        sc2     <- addHook ref sc (cleanup r)
        pure (Done sc2 $ Succeeded r)

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
          Done outScope o => do
            nextScope <- fromMaybe outScope <$> findScope ref rs
            when closeAfterUse (close ref cur.id)
            pure $ Done nextScope o

      -- This just returns the current scope.
      GScope => pure (Done sc $ Succeeded sc)

      -- Continues running the given pull in the given scope.
      IScope sc2 p => step p sc2

  covering
  loop : EmptyPull f es r -> Scope f -> f [] (Outcome es r)
  loop p sc =
    step p sc >>= \case
      Done _ v      => pure v
      Out  sc2 _ p2 => loop p2 sc2

parameters {auto mcn : MCancel f}
           {auto tgt : Target s f}

  export covering
  runIn : Scope f -> EmptyPull f es r -> f [] (Outcome es r)
  runIn sc p = do
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
  run : EmptyPull f es r -> f [] (Outcome es r)
  run p =
    bracket newScope
      (\(sc,ref) => loop ref p sc)
      (\(sc,ref) => close ref sc.id)

||| Convenience alias of `run` for running a `Pull` in the `Elin s`
||| monad, producing a pure result.
export %inline covering
pullElin : (forall s . EmptyPull (Elin s) es r) -> Outcome es r
pullElin f = either absurd id $ runElin (run f)
