module FS.Pull

import public Data.Linear.ELift1
import public FS.ChunkSize

import Control.Monad.Elin

import Data.Linear.Ref1
import Data.List
import Data.Maybe
import Data.Nat

import FS.Internal.Chunk
import FS.Scope

%default total

--------------------------------------------------------------------------------
-- Pull Type
--------------------------------------------------------------------------------

||| A `Pull f o es r` is a - possibly infinite - series of effectful
||| computations running in monad `f`, producing an arbitrary sequence
||| of chunks of values of type `o` along the way, that eventually
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
       (f : List Type -> Type -> Type)
    -> (o : Type)
    -> (es : List Type)
    -> (r : Type)
    -> Type where

  ||| Constructor for producing value of type `r`
  Val    : (res : r) -> Pull f o es r

  ||| Constructor for failing with an exception
  Err    : HSum es -> Pull f o es r

  ||| Constructor for producing a chunk of output values
  Output : (val : List o) -> Pull f o es ()

  ||| Wraps an arbitrary effectful computation in a `Pull`
  Eval   : (act : f es r) -> Pull f o es r

  ||| Unwraps the given child `Pull` until it either produces
  ||| a result or a chunk of output.
  Uncons : Pull f o es r -> Pull f q es (Either r (List o, Pull f o es r))

  ||| Attempts to evaluate the underlying `Pull`, returning any error
  ||| wrapped in a `Left` and a successful result in a `Right`. This is
  ||| the primitive used for error handling.
  Att    : Pull f o es r -> Pull f o fs (Result es r)

  ||| Sequencing of `Pull`s via monadic bind `(>>=)`.
  Bind   : Pull f o es r -> (r -> Pull f o es s) -> Pull f o es s

  ||| Runs the given `Pull` in a new child scope. The optional second argument
  ||| is used to check, if the scope has been interrupted.
  OScope : Pull f o es r -> Maybe (f [] Bool) -> Pull f o es r

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
output1 : o -> Pull f o es ()
output1 v = Output [v]

||| Emits a list of values
export %inline
output : List o -> Pull f o es ()
output [] = pure ()
output vs = Output vs

||| Emits values from an arbitrary foldable
export %inline
foldable : Foldable m => m o -> Pull f o es ()
foldable = output . toList

||| Like `unfold` but emits values in larger chunks.
|||
||| This allows us to potentially emit a bunch of values right before
||| we are done.
export
unfoldChunk : (init : s) -> (s -> (List o, Either r s)) -> Pull f o es r
unfoldChunk init g =
  assert_total $ case g init of
    (os, Left r)   => output os $> r
    (os, Right s2) => output os >> unfoldChunk s2 g

||| Emits values until the given generator function returns a `Left`
export %inline
unfold : ChunkSize => (init : s) -> (s -> Either r (o,s)) -> Pull f o es r
unfold @{CS n} init g = unfoldChunk init (unfoldImpl [<] n g)

||| Like `unfoldMaybe` but emits values in chunks.
export
unfoldChunkMaybe : (init : s) -> (s -> (List o, Maybe s)) -> Pull f o es ()
unfoldChunkMaybe init g =
  let (os,ms) := g init
   in case ms of
        Nothing => output os
        Just s2 => assert_total $ output os >> unfoldChunkMaybe s2 g

||| Generates a stream from the given list of chunks. Empty chunks
||| will be silently dropped.
export
fromChunks : List (List o) -> Pull f o es ()
fromChunks vss =
  unfoldChunkMaybe vss $ \case
    []   => ([], Nothing)
    h::t => (h, Just t)

||| Like `unfold` but does not produce an interesting result.
export %inline
unfoldMaybe : ChunkSize => (init : s) -> (s -> Maybe (o,s)) -> Pull f o es ()
unfoldMaybe @{CS n} init g = unfoldChunkMaybe init (unfoldMaybeImpl [<] n g)

||| Like `unfold` but produces values via an effectful computation
||| until a `Left` is returned.
export
unfoldEval : f es (Either r o) -> Pull f o es r
unfoldEval act =
  assert_total $ Eval act >>= \case
    Left r  => pure r
    Right o => output1 o >> unfoldEval act

||| Like `unfold` but produces values via an effectful computation
||| until a `Nothing` is returned.
export
unfoldEvalMaybe : f es (Maybe o) -> Pull f o es ()
unfoldEvalMaybe act =
  assert_total $ Eval act >>= \case
    Nothing => pure ()
    Just o  => output1 o >> unfoldEvalMaybe act

||| Like `unfoldEval` but produces values via an effectful computation
||| until the given function returns a `Just`.
export
unfoldEvalChunk : f es (List o, Maybe r) -> Pull f o es r
unfoldEvalChunk act =
  assert_total $ Eval act >>= \case
    (vs, Just r)  => output vs $> r
    (vs, Nothing) => output vs >> unfoldEvalChunk act

||| Like `unfoldEval` but produces values via an effectful computation
||| until the given function returns a `Nothing`.
export
unfoldEvalChunkMaybe : f es (Maybe $ List o) -> Pull f o es ()
unfoldEvalChunkMaybe act =
  assert_total $ Eval act >>= \case
    Nothing => pure ()
    Just vs => output vs >> unfoldEvalChunkMaybe act

||| Infinitely cycles through the given `Pull`
export
repeat : Pull f o es () -> Pull f o es ()
repeat v = assert_total $ v >> repeat v

||| Infinitely produces chunks of values of the given size
export
fill : ChunkSize => o -> Pull f o es ()
fill @{CS n} v = let vs := replicate n v in repeat (output vs)

||| An infinite stream of values of type `o` where
||| the next value is built from the previous one by
||| applying the given function.
export %inline
iterate : ChunkSize => o -> (o -> o) -> Pull f o es ()
iterate @{CS n} v f = unfoldChunkMaybe v (iterateImpl [<] n f)

||| Produces the given value `n` times as chunks of the given size.
export
replicate : ChunkSize => Nat -> o -> Pull f o es ()
replicate @{CS n} m v =
  case m >= n of
    False => output (replicate m v)
    True  => go (m `minus` n) (replicate n v)

  where
    go : Nat -> List o -> Pull f o es ()
    go rem vs =
      case rem >= n of
        False => output vs >> output (replicate rem v)
        True  => output vs >> go (assert_smaller rem $ rem `minus` n) vs

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

||| Prepends a list of values to a `Pull`
export %inline
cons : List o -> Pull f o es r -> Pull f o es r
cons [] p = p
cons vs p = Output vs >> p

||| Splits the first chunk of values from the head of a `Pull`, returning
||| either the final result or a list of values plus the remainder of the
||| `Pull`.
|||
||| Please note that the resulting pull with not produce any output.
export %inline
uncons : Pull f o es r -> Pull f q es (Either r (List o, Pull f o es r))
uncons = Uncons

||| Splits the very value from the head of a `Pull`
export
uncons1 : Pull f o es r -> Pull f q es (Either r (o, Pull f o es r))
uncons1 p =
  assert_total $ uncons p >>= \case
    Left x => pure (Left x)
    Right (vs,q) => case vs of
      []   => uncons1 q
      h::t => pure (Right (h, cons t q))

||| Like `uncons`, but pairs the tail of the `Pull` with the `Scope`
||| it should be run in.
|||
||| Use this for evaluating several `Pull`s in parallel, for instance
||| when zipping or merging them. This will make sure that all resources
||| will be released in the correct order.
export
stepLeg : StepLeg f es o -> Pull f q es (Maybe (List o, StepLeg f es o))
stepLeg (SL p sc) =
  inScope sc $ do
    uncons p >>= \case
      Left _       => pure Nothing
      Right (v,tl) => (\sc => Just (v, SL tl sc)) <$> scope

||| Utility for consing some values onto a pull and running it in
||| its desired scope.
export
endLeg : List o -> StepLeg f es o -> Pull f o es ()
endLeg vs (SL p sc) = inScope sc (cons vs p)

||| Like `uncons`, but returns a chunk of at most `n` elements
export
unconsLimit :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> Pull f o es ()
  -> Pull f q es (Maybe (List o, Pull f o es ()))
unconsLimit n p =
  uncons p >>= \case
    Left _       => pure Nothing
    Right (os,q) =>
     let (pre,pst) := splitAtImpl [<] os n
      in pure (Just (pre, cons pst q))

||| Like `uncons`, but returns a chunk of at least `n` elements
export
unconsMin :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> (allowFewer : Bool)
  -> Pull f o es ()
  -> Pull f q es (Maybe (List o, Pull f o es ()))
unconsMin n af = go [<] n
  where
    go :
         SnocList o
      -> Nat
      -> Pull f o es ()
      -> Pull f q es (Maybe (List o, Pull f o es ()))
    go so n p =
      assert_total $ uncons p >>= \case
        Left _ => case so <>> [] of
          [] => pure Nothing
          os => if af then pure $ Just (os, pure ()) else pure Nothing
        Right (os,q) => case n `minus` length os of
          0  => pure $ Just (so <>> os, q)
          n2 => go (so <>< os) n2 q

||| Like `uncons` but returns a chunk of exactly `n` elements
export
unconsN :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> (allowFewer : Bool)
  -> Pull f o es ()
  -> Pull f q es (Maybe (List o, Pull f o es ()))
unconsN n af p =
  map
    (map (\(os,q) => let (x,y) := splitAtImpl [<] os n in (x, cons y q)))
    (unconsMin n af p)

||| Emits the first `n` values of a `Pull`, returning the
||| remainder.
export
take : Nat -> Pull f o es () -> Pull f o es (Maybe $ Pull f o es ())
take 0 p = pure (Just p)
take k p =
  assert_total $ uncons p >>= \case
    Left _      => pure Nothing
    Right (o,q) =>
      let (k2,o2,rem) := takeImpl [<] k o
       in cons o2 (take k2 $ cons rem q)

||| Returns the last value emitted by a pull
export
last : Pull f o es () -> Pull f q es (Maybe o)
last = go Nothing
  where
    go : Maybe o -> Pull f o es () -> Pull f q es (Maybe o)
    go m p =
      assert_total $ uncons p >>= \case
        Left _         => pure m
        Right ([],q)   => go m q
        Right (h::t,q) => go (Just $ foldl (\_,v => v) h t) q

||| Like `uncons` but does not consume the chunk
export
peek : Pull f o es () -> Pull f q es (Maybe (List o, Pull f o es ()))
peek p =
  uncons p >>= \case
    Left _       => pure Nothing
    Right (vs,q) => pure $ Just (vs, cons vs q)

||| Like `uncons1` but does not consume the value
export
peek1 : Pull f o es () -> Pull f q es (Maybe (o, Pull f o es ()))
peek1 p =
  assert_total $ uncons p >>= \case
    Left _              => pure Nothing
    Right (vs@(h::_),q) => pure $ Just (h, cons vs q)
    Right ([],q)        => peek1 q

||| Drops up to `n` values from a stream returning the remainder
||| if it has not already been exhausted.
export
drop : Nat -> Pull f o es () -> Pull f o es (Maybe $ Pull f o es ())
drop 0 p = pure (Just p)
drop k p =
  assert_total $ uncons p >>= \case
    Left _      => pure Nothing
    Right (o,p) =>
      let (k2,o2) := dropImpl k o
       in case o2 of
            [] => drop k2 p
            _  => pure (Just $ cons o2 p)

takeWhile_ :
     (takeFailure : Bool)
  -> (o -> Bool)
  -> Pull f o es r
  -> Pull f o es (Maybe $ Pull f o es r)
takeWhile_ tf pred p =
  assert_total $ uncons p >>= \case
    Left _      => pure Nothing
    Right (o,p) => case takeWhileImpl tf [<] pred o of
      Nothing    => cons o $ takeWhile_ tf pred p
      Just (l,r) => output l $> Just (cons r p)

||| Emits values until the given predicate returns `False`,
||| returning the remainder of the `Pull`.
export %inline
takeWhile :
     (o -> Bool)
  -> Pull f o es r
  -> Pull f o es (Maybe $ Pull f o es r)
takeWhile = takeWhile_ False

||| Like `takeWhile` but also includes the first failure.
export %inline
takeThrough :
     (o -> Bool)
  -> Pull f o es r
  -> Pull f o es (Maybe $ Pull f o es r)
takeThrough = takeWhile_ True

||| Emits the last `n` elements of the input
|||
||| Note: The whole `n` values have to be kept in memory, therefore,
|||       the result will be emitted as a single chunk. Take memory
|||       consumption into account when using this for very large `n`.
export
takeRight :
     (n : Nat)
  -> {auto 0 p : IsSucc n}
  -> Pull f o es ()
  -> Pull f q es (List o)
takeRight n = go []
  where
    go : List o -> Pull f o es () -> Pull f q es (List o)
    go xs p =
      assert_total $ unconsN n True p >>= \case
        Nothing     => pure xs
        Just (ys,q) => go (drop (length ys) xs ++ ys) q

dropWhile_ :
     (dropFailure : Bool)
  -> (o -> Bool)
  -> Pull f o es ()
  -> Pull f o es (Maybe $ Pull f o es ())
dropWhile_ df pred p =
  assert_total $ uncons p >>= \case
    Left _      => pure Nothing
    Right (o,p) => case dropWhileImpl pred o of
      []   => dropWhile_ df pred p
      h::t => case df of
        True  => pure $ Just (cons t p)
        False => pure $ Just (Output (h::t) >> p)

||| Drops values from a stream while the given predicate returns `True`,
||| returning the remainder of the stream (if any).
export
dropWhile :
     (o -> Bool)
  -> Pull f o es ()
  -> Pull f o es (Maybe $ Pull f o es ())
dropWhile = dropWhile_ False

||| Like `dropWhile` but also drops the first value where
||| the predicate returns `False`.
export
dropThrough :
     (o -> Bool)
  -> Pull f o es ()
  -> Pull f o es (Maybe $ Pull f o es ())
dropThrough = dropWhile_ True

||| Returns the first value fulfilling the given predicate
||| together with the remainder of the stream.
export
find : (o -> Bool) -> Pull f o es () -> Pull f p es (Maybe (o, Pull f o es ()))
find pred p =
  assert_total $ uncons p >>= \case
    Left _       => pure Nothing
    Right (os,q) => case findImpl pred os of
      Just (v,rem) => pure (Just (v, cons rem q))
      Nothing      => find pred q

||| Chunk-wise maps the output of a `Pull`
export
mapChunks : (List o -> List p) -> Pull f o es r -> Pull f p es r
mapChunks f p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (v,p) => cons (f v) $ mapChunks f p

||| Chunk-wise effectful mapping of the output of a `Pull`
export
mapChunksEval : (List o -> f es (List p)) -> Pull f o es r -> Pull f p es r
mapChunksEval f p =
  assert_total $ uncons p >>= \case
    Left x       => pure x
    Right (vs,p) => do
      ws <- Eval (f vs)
      cons ws $ mapChunksEval f p

||| Maps the output of a `Pull`
export %inline
mapOutput : (o -> p) -> Pull f o es r -> Pull f p es r
mapOutput = mapChunks . map

||| Filters the output of a `Pull` emitting only the
||| values that fulfill the given predicate
export %inline
filter : (o -> Bool) -> Pull f o es r -> Pull f o es r
filter = mapChunks . filter

||| Folds all input chunk-wise using an initial value and
||| binary operator
export
foldChunks : p -> (p -> List o -> p) -> Pull f o es () -> Pull f q es p
foldChunks v g s =
  assert_total $ uncons s >>= \case
    Left _        => pure v
    Right (vs,s2) => foldChunks (g v vs) g s2

||| Folds all input using an initial value and binary operator
export %inline
fold : p -> (p -> o -> p) -> Pull f o es () -> Pull f q es p
fold v = foldChunks v . foldl

||| Folds all input using the supplied binary operator.
|||
||| This returns `Nothing` in case the stream does not produce any
||| values.
export %inline
fold1 : (o -> o -> o) -> Pull f o es () -> Pull f q es (Maybe o)
fold1 g p =
  assert_total $ uncons p >>= \case
    Left _         => pure Nothing
    Right (h::t,q) => Just <$> fold (foldl g h t) g q
    Right ([],q)   => fold1 g q

||| Returns `True` if all emitted values of the given stream fulfill
||| the given predicate
export
all : (o -> Bool) -> Pull f o es () -> Pull f q es Bool
all pred p =
  assert_total $ uncons p >>= \case
    Left _ => pure True
    Right (vs,q) => case all pred vs of
      True  => all pred q
      False => pure False

||| Returns `True` if any of the emitted values of the given stream fulfills
||| the given predicate
export
any : (o -> Bool) -> Pull f o es () -> Pull f q es Bool
any pred p =
  assert_total $ uncons p >>= \case
    Left _ => pure False
    Right (vs,q) => case any pred vs of
      False  => any pred q
      True   => pure True

||| General stateful conversion of a `Pull`s output.
|||
||| Aborts as soon as the given accumulator function returns `Nothing`
export
scanChunksMaybe :
     s
  -> (s -> Maybe (List o -> (List p,s)))
  -> Pull f o es ()
  -> Pull f p es s
scanChunksMaybe s1 f p =
  assert_total $ case f s1 of
    Nothing => pure s1
    Just g  => uncons p >>= \case
      Left r      => pure s1
      Right (v,p) => let (w,s2) := g v in cons w $ scanChunksMaybe s2 f p

||| Like `scanChunksMaybe` but will transform the whole output.
export
scanChunks :
     s
  -> (s -> List o -> (List p,s))
  -> Pull f o es ()
  -> Pull f p es s
scanChunks s1 f = scanChunksMaybe s1 (Just . f)

export
unconsBind : Pull f o es () -> (List o -> Pull f p es ()) -> Pull f p es ()
unconsBind p g =
  assert_total $ uncons p >>= \case
    Left _       => pure ()
    Right (os,q) => g os >> unconsBind q g

export
bindOutput : (List o -> Pull f p es ()) -> Pull f o es () -> Pull f p es ()
bindOutput f p =
  assert_total $ uncons p >>= \case
    Left _      => pure ()
    Right (v,q) => f v >> bindOutput f q

export
bindOutput1 : (o -> Pull f p es ()) -> Pull f o es () -> Pull f p es ()
bindOutput1 f p =
  assert_total $ uncons1 p >>= \case
    Left _      => pure ()
    Right (v,q) => f v >> bindOutput1 f q

export
attemptOutput : Pull f o es () -> Pull f (Result es o) fs ()
attemptOutput p =
  Att (mapOutput Right p) >>= \case
    Left x  => output1 (Left x)
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
  Done : (ss : Scope f) -> (res : r) -> StepRes f o es r

  ||| Stream produced some output
  Out  : (ss : Scope f) -> (chunk : List o) -> Pull f o es r -> StepRes f o es r

  ||| Stream was interrupted
  End  : (ss : Scope f) -> StepRes f o es r

parameters {0 f      : List Type -> Type -> Type}
           {auto eff : ELift1 s f}
           (ref      : Ref s (ScopeST f))

  ||| A single evaluation step of a `Pull`.
  |||
  ||| Either returns the final result or the next chunk of output
  ||| paired with the remainder of the `Pull`. Fails with an error in
  ||| case of an uncaught exception. Returns `End` in case the current
  ||| scope was interrupted.
  -- Implementation note: This is a pattern match on the different
  -- data constructors of `Pull`. The `Scope` argument is the resource
  -- scope we are currently working with.
  export covering
  step : Pull f o es r -> Scope f -> f es (StepRes f o es r)
  step p sc = do
    False <- isInterrupted sc | True => pure (End sc)
    case p of
      -- We got a final result, so we just return it.
      Val res    => pure (Done sc res)

      -- An exception occured so we raise it in the `f` monad.
      Err x      => fail x

      -- The pull produced som output. We return it together with an
      -- empty continuation.
      Output val => pure $ Out sc val (pure ())

      -- We evaluate the given effect, wrapping it in a `Done` in
      -- case it succeeds.
      Eval act   => Done sc <$> act

      -- We step the wrapped pull. In case it produces some output,
      -- we wrap the output and continuation in a `Done . Right`. In case
      -- it is exhausted (produces an `Out res` we wrap the `res` in
      -- a `Done . Left`. In case it was interrupted, we pass on the `End sc`.
      Uncons p   =>
        step p sc >>= \case
          Done sc res     => pure (Done sc $ Left res)
          Out  sc chunk x => pure (Done sc $ Right (chunk, x))
          End sc          => pure (End sc)

      -- We try and step the wrapped pull. In case of an error, we wrap
      -- it in a `Done . Left`. In case of a final result, we return the
      -- result wrapped ina `Done . Right`. In case of more output,
      -- the output is returned and the continuation pull is again wrapped
      -- in an `Att`. This makes sure that the pull produces output until
      -- the first error or it is exhausted or interrputed.
      Att {fs} x =>
        attempt {fs} (step x sc) >>= \case
          Left y  => pure (Done sc $ Left y)
          Right y => case y of
            Done ss res    => pure (Done ss $ Right res)
            Out ss chunk z => pure (Out ss chunk (Att z))
            End ss         => pure (End ss)

      -- Monadic bind: We step the wrapped pull, passing the final result
      -- to function `g`. In case of some output being emitted, we return
      -- the output and wrap the continuation again in a `Bind`. In case
      -- of interruption, we pass on the interruption.
      Bind x g   =>
        step x sc >>= \case
          Done sc r  => step (g r) sc
          Out sc v p => pure $ Out sc v (Bind p g)
          End sc     => pure (End sc)

      -- Runs pull in a new child scope. The scope is setup and registered,
      -- and the result wrapped in a `WScope`.
      OScope p ir =>
        openScope ref ir sc >>= \sc2 =>
          step (WScope p sc2.id sc.id) sc2

      -- Acquires some resource in the current scope and adds its
      -- cleanup hook to the current scope.
      Acquire alloc cleanup => do
        res <- alloc
        sc2 <- addHook ref sc (cleanup res)
        pure (Done sc2 res)

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
        attempt (step p cur) >>= \case
          Right (Out scope hd tl) => pure (Out scope hd $ WScope tl id rs)
          Right (End outScope)    => do
            nextScope <- fromMaybe outScope <$> findScope ref rs
            when closeAfterUse (weakenErrors $ close ref cur.id)
            pure $ End nextScope
          Right (Done outScope r) => do
            nextScope <- fromMaybe outScope <$> findScope ref rs
            when closeAfterUse (weakenErrors $ close ref cur.id)
            pure $ Done nextScope r
          Left  x => do
            when closeAfterUse (weakenErrors $ close ref cur.id)
            fail x

      -- This just returns the current scope.
      GScope => pure (Done sc sc)

      -- Continues running the given pull in the given scope.
      IScope sc2 p => step p sc2

  covering
  loop : Pull f Void es r -> Scope f -> f es (Maybe r)
  loop p sc =
    step p sc >>= \case
      Done _ v       => pure (Just v)
      End  _         => pure Nothing
      Out  sc2 [] p2 => loop p2 sc2

||| Runs a `Pull` to completion, eventually producing
||| a value of type `r`.
|||
||| Note: In case of an infinited stream, this will loop forever.
|||       In order to cancel the evaluation, consider using
|||       `Async` and racing it with a cancelation thread (for instance,
|||       by waiting for an operating system signal).
export covering
run : ELift1 s f => Pull f Void es r -> f [] (Outcome es r)
run p = do
  ref <- newref Scope.empty
  sc  <- root {es = []} ref
  res <- attempt {fs = []} (loop ref p sc)
  close ref sc.id
  pure $ case res of
    Right Nothing  => Canceled
    Right (Just v) => Succeeded v
    Left x         => Error x

||| Convenience alias of `run` for running a `Pull` in the `Elin s`
||| monad, producing a pure result.
export %inline covering
pullElin : (forall s . Pull (Elin s) Void es r) -> Outcome es r
pullElin f = either absurd id $ runElin (run f)

