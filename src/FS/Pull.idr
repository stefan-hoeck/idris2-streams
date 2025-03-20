module FS.Pull

import Control.Monad.MCancel
import Control.Monad.Resource

import Data.SnocList

import public FS.Core

%default total

--------------------------------------------------------------------------------
-- Creating Pulls
--------------------------------------------------------------------------------

public export
data UnfoldRes : (r,s,o : Type) -> Type where
  More : (vals : o) -> (st : s) -> UnfoldRes r s o
  Done : (res : r) ->  UnfoldRes r s o
  Last : (res : r) ->  (vals : o) -> UnfoldRes r s o

||| Emits a list of chunks.
export %inline
emits : List o -> Stream f es o
emits []     = pure ()
emits (h::t) = emit h >> emits t

||| Emits a list of values as a single chunk.
export
emitList : List o -> Stream f es (List o)
emitList [] = pure ()
emitList vs = emit vs

||| Emits a single optional value.
export
emitMaybe : Maybe o -> Stream f es o
emitMaybe Nothing  = pure ()
emitMaybe (Just v) = emit v

||| Utility to emit a single list chunk from a snoc list.
export %inline
emitSnoc : SnocList o -> Maybe o -> Stream f es (List o)
emitSnoc sv m = emitList $ (sv <>> maybe [] pure m)

||| Emits a single chunk of output generated from an effectful
||| computation.
export %inline
eval : f es o -> Stream f es o
eval act = exec act >>= emit

||| Like `unfold` but emits values in larger chunks.
|||
||| This allows us to potentially emit a bunch of values right before
||| we are done.
export
unfoldC : (init : s) -> (s -> UnfoldRes r s o) -> Pull f o es r
unfoldC init g =
  assert_total $ case g init of
    More vals st => emit vals >> unfoldC st g
    Done res      => pure res
    Last res vals => emit vals $> res

||| Like `unfoldC` but produces values via an effectful computation
||| until a `Done` or `Last` is returned.
export
unfoldEval : (init : s) -> (s -> f es (UnfoldRes r s o)) -> Pull f o es r
unfoldEval cur act =
  assert_total $ Exec (act cur) >>= \case
    More vals st => emit vals >> unfoldEval st act
    Done res      => pure res
    Last res vals => emit vals $> res

||| Produces values via an effectful computation
||| until a `Nothing` is returned.
export
unfoldEvalMaybe : f es (Maybe o) -> Stream f es o
unfoldEvalMaybe act =
  assert_total $ Exec act >>= \case
    Nothing => pure ()
    Just o  => emit o >> unfoldEvalMaybe act

||| Infinitely produces chunks of values of the given size
export
fillC : o -> Stream f es o
fillC v = assert_total $ emit v >> fillC v

||| An infinite stream of values of type `o` where
||| the next value is built from the previous one by
||| applying the given function.
export
iterateC : o -> (o -> o) -> Stream f es o
iterateC v f = unfoldC v (\x => More x $ f x)

||| Produces the given chunk of value `n` times.
export
replicateC : Nat -> o -> Stream f es o
replicateC 0     _ = pure ()
replicateC (S k) v = emit v >> replicateC k v

||| Infinitely cycles through the given `Pull`
export
repeat : Stream f es o -> Stream f es o
repeat v = assert_total $ v >> repeat v

||| Prepends the given output to a pull.
export %inline
cons : o -> Pull f o es r -> Pull f o es r
cons vs p = Output vs >> p

||| Prepends the given optional output to a pull.
export %inline
consMaybe : Maybe o -> Pull f o es r -> Pull f o es r
consMaybe (Just v) p = cons v p
consMaybe Nothing  p = p

--------------------------------------------------------------------------------
-- Splitting Streams
--------------------------------------------------------------------------------

||| Splits the first chunk of values from the head of a `Pull`, returning
||| either the final result or a list of values plus the remainder of the
||| `Pull`.
export %inline
uncons : Pull f o es r -> Pull f q es (Either r (o, Pull f o es r))
uncons = Uncons

||| Result of splitting a value into two parts. This is used to
||| split up streams of data along logical boundaries.
public export
data BreakRes : (c : Type) -> Type where
  ||| The value was broken and we got a (possibly empty) pre- and postfix.
  Broken : (pre, post : Maybe c) -> BreakRes c
  ||| The value could not be broken.
  Keep   : c -> BreakRes c

||| Uses the given breaking function to break the pull into
||| a prefix of emitted chunks and a suffix that is returned as
||| the result.
export
breakPull : (o -> BreakRes o) -> Pull f o es r -> Pull f o es (Pull f o es r)
breakPull g p =
  assert_total $ uncons p >>= \case
    Left r      => pure (pure r)
    Right (v,q) => case g v of
      Broken pre post => emitMaybe pre $> consMaybe post q
      Keep w          => emit w >> breakPull g q

||| Uses the given breaking function to break the pull into
||| a stream of lists of values.
export
splitPull : (o -> BreakRes p) -> Pull f o es r -> Pull f (List p) es r
splitPull g = go [<]
  where
    go : SnocList p -> Pull f o es r -> Pull f (List p) es r
    go sp pl =
      assert_total $ uncons pl >>= \case
        Left r      => emitSnoc sp Nothing $> r
        Right (v,q) => case g v of
          Broken pre post => emitSnoc sp pre >> go (maybe [<] pure post) q
          Keep w          => go (sp :< w) q

||| Emits only the first `n` chunks of values of a `Stream`.
export
takeC : Nat -> Stream f es o -> Stream f es o
takeC n = newScope . go n
  where
    go : Nat -> Stream f es o -> Stream f es o
    go 0     _ = pure ()
    go (S k) p =
      uncons p >>= \case
        Left _      => pure ()
        Right (v,q) => emit v >> go k q

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

takeWhile_ : (takeFail : Bool) -> (o -> Bool) -> Stream f es o -> Stream f es o
takeWhile_ tf pred = newScope . go
  where
    go : Stream f es o -> Stream f es o
    go p =
      assert_total $ uncons p >>= \case
        Left v      => pure ()
        Right (o,p) => case pred o of
          True  => emit o >> go p
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
takeWhileJust = newScope . go
  where
    go : Stream f es (Maybe o) -> Stream f es o
    go p =
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

--------------------------------------------------------------------------------
-- Maps and Filters
--------------------------------------------------------------------------------

||| Maps chunks of output via a partial function.
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

||| Chunk-wise filters the emit of a `Pull` emitting only the
||| values that fulfill the given predicate
export
filterC : (o -> Bool) -> Pull f o es r -> Pull f o es r
filterC pred p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (v,q) => case pred v of
      True  => emit v >> filterC pred q
      False => filterC pred q

||| Convenience alias for `filterC (not . pred)`.
export %inline
filterNotC : (o -> Bool) -> Pull f o es r -> Pull f o es r
filterNotC pred = filterC (not . pred)

||| Wraps the values emitted by this stream in a `Just` and
||| marks its end with a `Nothing`.
export
endWithNothing : Pull f o es r -> Pull f (Maybe o) es r
endWithNothing s = mapC Just s >>= \res => emit Nothing $> res

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

||| Returns the first output of this stream.
export
firstOr : Lazy o -> Stream f es o -> Pull f p es o
firstOr dflt s =
  newScope $ uncons s >>= \case
    Left _      => pure dflt
    Right (v,_) => pure v

||| Folds the emit of a pull using an initial value and binary operator.
|||
||| The accumulated result is emitted as a single value.
export
foldC : (p -> o -> p) -> p -> Pull f o es r -> Pull f p es r
foldC g v s =
  assert_total $ uncons s >>= \case
    Left res      => emit v $> res
    Right (vs,s2) => foldC g (g v vs) s2

||| Like `foldC` but will not emit a value in case of an empty pull.
export
fold1C : (o -> o -> o) -> Pull f o es r -> Pull f o es r
fold1C g s =
  uncons s >>= \case
    Left r      => pure r
    Right (v,q) => foldC g v q

||| Emits `True` if all emitted values of the given stream fulfill
||| the given predicate
export
allC : (o -> Bool) -> Stream f es o -> Stream f es Bool
allC pred p =
  assert_total $ uncons p >>= \case
    Left _ => emit True
    Right (vs,q) => case pred vs of
      True  => allC pred q
      False => emit False

||| Returns `True` if any of the emitted values of the given stream fulfills
||| the given predicate
export
anyC : (o -> Bool) -> Stream f es o -> Stream f es Bool
anyC pred p =
  assert_total $ uncons p >>= \case
    Left _ => emit False
    Right (vs,q) => case pred vs of
      False  => anyC pred q
      True   => emit True

||| Sums up the emitted chunks.
export %inline
sumC : Num o => Pull f o es r -> Pull f o es r
sumC = foldC (+) 0

||| Counts the number of emitted chunks.
export %inline
countC : Pull f o es r -> Pull f Nat es r
countC = foldC (const . S) 0

||| Emits the largest output encountered.
export %inline
maximumC : Ord o => Pull f o es r -> Pull f o es r
maximumC = fold1C max

||| Emits the smallest output encountered.
export %inline
minimumC : Ord o => Pull f o es r -> Pull f o es r
minimumC = fold1C min

||| Emits the smallest output encountered.
export %inline
mappendC : Semigroup o => Pull f o es r -> Pull f o es r
mappendC = fold1C (<+>)

||| Accumulates the emitted values over a monoid.
|||
||| Note: This corresponds to a left fold, so it will
|||       run in quadratic time for monoids that are
|||       naturally accumulated from the right (such as List)
export %inline
foldMapC : Monoid m => (o -> m) -> Pull f o es r -> Pull f m es r
foldMapC f = foldC (\v,el => v <+> f el) neutral

--------------------------------------------------------------------------------
-- Scans
--------------------------------------------------------------------------------

||| Runs a stateful computation across all chunks of data.
export
scanC : s -> (s -> o -> (p,s)) -> Pull f o es r -> Pull f p es r
scanC s1 f p =
  assert_total $ uncons p >>= \case
    Left res    => pure res
    Right (v,q) => let (w,s2) := f s1 v in emit w >> scanC s2 f q

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

||| Like `scan` but will possibly also emit the final state.
export
scanFull :
     s
  -> (s -> o -> (p,s))
  -> (s -> Maybe p)
  -> Stream f es o
  -> Stream f es p
scanFull s1 f last p = do
  v <- scanMaybe s1 (Just . f) p
  case last v of
    Just rem => emit rem
    Nothing  => pure ()

--------------------------------------------------------------------------------
-- Resource Management
--------------------------------------------------------------------------------

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
--
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

||| Converts every chunk of output to a new stream,
||| concatenating the resulting streams before emitting the final
||| result.
export
flatMapC : Pull f o es r -> (o -> Stream f es p) -> Pull f p es r
flatMapC p g =
  assert_total $ uncons p >>= \case
    Left v       => pure v
    Right (os,q) => g os >> flatMapC q g

||| Flipped version of `flatMapC`
export %inline
bindC : (o -> Pull f p es ()) -> Pull f o es r -> Pull f p es r
bindC = flip flatMapC

export
attemptC : Pull f o es () -> Pull f (Result es o) fs ()
attemptC p =
  Att (mapC Right p) >>= \case
    Left x  => emit (Left x)
    Right _ => pure ()
