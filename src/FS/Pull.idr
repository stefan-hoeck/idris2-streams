||| General operations on `Pull`s
||| and `Stream`s: Splits, scans, filters, and maps
|||
||| It is suggested to import this qualified `import FS.Pull as P` or
||| via the catch-all module `FS` and use qualified names such
||| as `P.filter` for those functions that overlap with the ones
||| from `FS.Chunk`.
module FS.Pull

import Control.Monad.MCancel
import Control.Monad.Resource
import public FS.Core

import Data.SnocList

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
emits (h::t) = cons h (emits t)

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
|||
||| This overlaps with function `FS.Chunk.unfold`, so it is typically
||| used qualified: `P.unfold`.
export
unfold : (init : s) -> (s -> UnfoldRes r s o) -> Pull f o es r
unfold init g =
  case g init of
    More vals st => cons vals (unfold st g)
    Done res      => pure res
    Last res vals => cons vals (pure res)

||| Like `unfold` but produces values via an effectful computation
||| until a `Done` or `Last` is returned.
export
unfoldEval : (init : s) -> (s -> f es (UnfoldRes r s o)) -> Pull f o es r
unfoldEval cur act =
  assert_total $ exec (act cur) >>= \case
    More vals st => cons vals (unfoldEval st act)
    Done res      => pure res
    Last res vals => cons vals (pure res)

||| Produces values via an effectful computation
||| until a `Nothing` is returned.
export
unfoldEvalMaybe : f es (Maybe o) -> Stream f es o
unfoldEvalMaybe act =
  assert_total $ exec act >>= \case
    Nothing => pure ()
    Just o  => cons o (unfoldEvalMaybe act)

||| Infinitely produces chunks of values of the given size
export
fill : o -> Pull f o es ()
fill v = cons v (fill v)

||| An infinite stream of values of type `o` where
||| the next value is built from the previous one by
||| applying the given function.
export
iterate : o -> (o -> o) -> Pull f o es ()
iterate v f = unfold v (\x => More x $ f x)

||| Produces the given chunk of value `n` times.
export
replicate : Nat -> o -> Stream f es o
replicate 0     _ = pure ()
replicate (S k) v = cons v (replicate k v)

||| Infinitely cycles through the given `Pull`
export
repeat : Stream f es o -> Pull f o es ()
repeat v = assert_total $ v >> repeat v

||| Prepends the given optional output to a pull.
export %inline
consMaybe : Maybe o -> Pull f o es r -> Pull f o es r
consMaybe (Just v) p = cons v p
consMaybe Nothing  p = p

--------------------------------------------------------------------------------
-- Splitting Streams
--------------------------------------------------------------------------------

public export
data BreakInstruction : Type where
  ||| Take the first succeeding value as part of the emitted prefix
  TakeHit : BreakInstruction

  ||| Keep the succeeding value as part of the postfix.
  PostHit : BreakInstruction

  ||| Discard the succeeding value
  DropHit : BreakInstruction

||| Like `uncons` but does not consume the chunk
export
peek : Pull f o es r -> Pull f q es (Either r (o, Pull f o es r))
peek p =
  uncons p >>= \case
    Left v       => pure (Left v)
    Right (vs,q) => pure $ Right (vs, cons vs q)

||| Like `peeks` but only checks if the pull has been exhausted or not.
export %inline
peekRes : Pull f o es r -> Pull f q es (Either r (Pull f o es r))
peekRes = map (map snd) . peek

||| Empties a stream silently dropping all output.
export
drain : Pull f o es r -> Pull f q es r
drain p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (_,p) => drain p

||| Emits the first `n` values of a `Pull`, returning the remainder.
|||
||| In case the remaining pull is exhausted, with will wrap the
||| final result in a `Left`, otherwise, the (non-empty) remainder will be
||| wrapped in a right.
export
splitAt : Nat -> Pull f o es r -> Pull f o es (Pull f o es r)
splitAt 0     p = pure p
splitAt (S k) p =
  assert_total $ uncons p >>= \case
    Left v      => pure (pure v)
    Right (v,q) => cons v (splitAt k q)

||| Emits only the first `n` values of a `Stream`.
export %inline
take : Nat -> Pull f o es r -> Stream f es o
take n = ignore . newScope . splitAt n

||| Like `take` but limits the number of emitted values.
|||
||| This fails with the given error in case the limit is exceeded.
|||
||| Note: This tries to read past the end of a pull by invoking `peekRes`.
|||       This is not suitable for limitting the input from a stream that
|||       blocks once it is exhausted.
export %inline
limit : Has e es => Lazy e -> Nat -> Pull f o es r -> Pull f o es r
limit err n p = do
  q      <- splitAt n p
  Left v <- peekRes q | Right _ => throw err
  pure v

||| Discards the first `n` values of a `Stream`, returning the
||| remainder.
export %inline
drop : Nat -> Pull f o es r -> Pull f o es r
drop k q = join $ drain (splitAt k q)

||| Only keeps the first element of the input.
export %inline
head : Pull f o es r -> Stream f es o
head = take 1

||| Drops the first element of the input.
export %inline
tail : Pull f o es r -> Pull f o es r
tail = drop 1

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
breakPull :
     (orElse : r -> Pull f o es r)
  -> (o -> BreakRes o)
  -> Pull f o es r
  -> Pull f o es (Pull f o es r)
breakPull orElse g p =
  assert_total $ uncons p >>= \case
    Left r      => pure (orElse r)
    Right (v,q) => case g v of
      Keep w         => cons w (breakPull orElse g q)
      Broken pre pst => consMaybe pre (pure $ consMaybe pst q)

||| Breaks a pull as soon as the given predicate returns `True`.
|||
||| The `BreakInstruction` dictates, if the value, for which the
||| predicate held, should be emitted as part of the prefix or the
||| suffix, or if it should be discarded.
export
breakFull :
     (orElse : r -> Pull f o es r)
  -> BreakInstruction
  -> (o -> Bool)
  -> Pull f o es r
  -> Pull f o es (Pull f o es r)
breakFull orElse bi pred =
  breakPull orElse $ \v => case pred v of
    False => Keep v
    True  => case bi of
      TakeHit => Broken (Just v) Nothing
      PostHit => Broken Nothing  (Just v)
      DropHit => Broken Nothing Nothing

||| Like `breakFull` but fails with the given execption if no
||| breaking point was found.
export %inline
forceBreakFull :
     {auto has : Has e es}
  -> (err : Lazy e)
  -> BreakInstruction
  -> (o -> Bool)
  -> Pull f o es r
  -> Pull f o es (Pull f o es r)
forceBreakFull err = breakFull (const $ throw err)

||| Emits values until the given predicate returns `True`.
|||
||| The `BreakInstruction` dictates, if the value, for which the
||| predicate held, should be emitted as part of the prefix or not.
export
takeUntil : BreakInstruction -> (o -> Bool) -> Pull f o es r -> Stream f es o
takeUntil tf pred = ignore . newScope . breakFull pure tf pred

||| Emits values until the given predicate returns `False`,
||| returning the remainder of the `Pull`.
export %inline
takeWhile : (o -> Bool) -> Pull f o es r -> Stream f es o
takeWhile pred = takeUntil DropHit (not . pred)

||| Like `takeWhile` but also includes the first failure.
export %inline
takeThrough : (o -> Bool) -> Pull f o es r -> Stream f es o
takeThrough pred = takeUntil TakeHit (not . pred)

||| Emits values until the given pull emits a `Nothing`.
export
takeWhileJust : Pull f (Maybe o) es r -> Stream f es o
takeWhileJust = newScope . go
  where
    go : Pull f (Maybe o) es r -> Stream f es o
    go p =
      assert_total $ uncons p >>= \case
        Left _      => pure ()
        Right (Just v,q)  => cons v (takeWhileJust q)
        Right (Nothing,q) => pure ()

||| Discards values until the given predicate returns `True`.
|||
||| The `BreakInstruction` dictates, if the value, for which the
||| predicate held, should be emitted as part of the remainder or not.
export
dropUntil : BreakInstruction -> (o -> Bool) -> Pull f o es r -> Pull f o es r
dropUntil tf pred p = drain (breakFull pure tf pred p) >>= id

||| Drops values from a stream while the given predicate returns `True`,
||| returning the remainder of the stream.
export %inline
dropWhile : (o -> Bool) -> Pull f o es r -> Pull f o es r
dropWhile pred = dropUntil PostHit (not . pred)

||| Like `dropWhile` but also drops the first value where
||| the predicate returns `False`.
export %inline
dropThrough : (o -> Bool) -> Pull f o es r -> Pull f o es r
dropThrough pred = dropUntil DropHit (not . pred)

--------------------------------------------------------------------------------
-- Maps and Filters
--------------------------------------------------------------------------------

||| Maps chunks of output via a partial function.
export
mapMaybe : (o -> Maybe p) -> Pull f o es r -> Pull f p es r
mapMaybe f p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (v,q) => case f v of
      Just w  => cons w (mapMaybe f q)
      Nothing => mapMaybe f q

||| Chunk-wise maps the emit of a `Pull`
export %inline
mapOutput : (o -> p) -> Pull f o es r -> Pull f p es r
mapOutput f = mapMaybe (Just . f)

||| Chunk-wise effectful mapping of the emit of a `Pull`
export
evalMap : (o -> f es p) -> Pull f o es r -> Pull f p es r
evalMap f p =
  assert_total $ uncons p >>= \case
    Left x       => pure x
    Right (vs,p) => do
      ws <- exec (f vs)
      cons ws (evalMap f p)

||| Chunk-wise effectful mapping of the emit of a `Pull`
export
evalMapMaybe : (o -> f es (Maybe p)) -> Pull f o es r -> Pull f p es r
evalMapMaybe f p =
  assert_total $ uncons p >>= \case
    Left x       => pure x
    Right (v,q) => do
      Just w <- exec (f v) | Nothing => evalMapMaybe f q
      cons w (evalMapMaybe f q)

||| Chunk-wise filters the emit of a `Pull` emitting only the
||| values that fulfill the given predicate
export
filter : (o -> Bool) -> Pull f o es r -> Pull f o es r
filter pred p =
  assert_total $ uncons p >>= \case
    Left x      => pure x
    Right (v,q) => case pred v of
      True  => cons v (filter pred q)
      False => filter pred q

||| Convenience alias for `filterC (not . pred)`.
export %inline
filterNot : (o -> Bool) -> Pull f o es r -> Pull f o es r
filterNot pred = filter (not . pred)

||| Wraps the values emitted by this stream in a `Just` and
||| marks its end with a `Nothing`.
export
endWithNothing : Pull f o es r -> Pull f (Maybe o) es r
endWithNothing s = mapOutput Just s >>= \res => cons Nothing (pure res)

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

||| Returns the first output of this stream and pairs it with the
||| result.
|||
||| The remainder of the pull is drained and run to completion.
export
pairLastOr : Lazy o -> Pull f o es r -> Pull f p es (o,r)
pairLastOr dflt s =
  assert_total $ uncons s >>= \case
    Left res    => pure (dflt,res)
    Right (v,q) => pairLastOr v q

||| Like `pairLastOr` but operates on a stream and therefore only returns
||| the last output.
export %inline
lastOr : Lazy o -> Stream f es o -> Pull f p es o
lastOr dflt s = fst <$> pairLastOr dflt s

||| Like `firstOr` but fails with the given error in case no
||| value is emitted.
export
pairLastOrErr : Has e es => Lazy e -> Pull f o es r -> Pull f p es (o,r)
pairLastOrErr err s =
  uncons s >>= \case
    Left res    => throw err
    Right (v,q) => pairLastOr v q

||| Like `pairLastOrErr` but operates on a stream and therefore only returns
||| the last output.
export %inline
lastOrErr : Has e es => Lazy e -> Stream f es o -> Pull f p es o
lastOrErr err s = fst <$> pairLastOrErr err s

||| Folds the emit of a pull using an initial value and binary operator.
|||
||| The accumulated result is emitted as a single value.
export
fold : (p -> o -> p) -> p -> Pull f o es r -> Pull f p es r
fold g v s =
  assert_total $ uncons s >>= \case
    Left res      => cons v (pure res)
    Right (vs,s2) => fold g (g v vs) s2

||| Like `fold` but instead of emitting the result as a single
||| value of output, it is paired with the `Pull`s result.
export
foldPair : (p -> o -> p) -> p -> Pull f o es r -> Pull f q es (p,r)
foldPair g v s =
  assert_total $ uncons s >>= \case
    Left res      => pure (v, res)
    Right (vs,s2) => foldPair g (g v vs) s2

||| Like `foldPair` but with a function that can fail.
export
foldPairE :
     {auto has : Has e es}
  -> (p -> o -> Either e p)
  -> p
  -> Pull f o es r
  -> Pull f q es (p,r)
foldPairE g v s =
  assert_total $ uncons s >>= \case
    Left res      => pure (v, res)
    Right (vs,s2) => case g v vs of
      Right v2 => foldPairE g v2 s2
      Left  x  => throw x

||| Convenience version of `foldPair` for working on streams.
export %inline
foldGet : (p -> o -> p) -> p -> Stream f es o -> Pull f q es p
foldGet acc ini = map fst . foldPair acc ini

||| Like `foldC` but will not emit a value in case of an empty pull.
export
fold1 : (o -> o -> o) -> Pull f o es r -> Pull f o es r
fold1 g s =
  uncons s >>= \case
    Left r      => pure r
    Right (v,q) => fold g v q

||| Emits `True` if all emitted values of the given stream fulfill
||| the given predicate
export
all : (o -> Bool) -> Pull f o es r -> Stream f es Bool
all pred p =
  assert_total $ uncons p >>= \case
    Left _ => emit True
    Right (vs,q) => case pred vs of
      True  => all pred q
      False => emit False

||| Returns `True` if any of the emitted values of the given stream fulfills
||| the given predicate
export
any : (o -> Bool) -> Pull f o es r -> Stream f es Bool
any pred p =
  assert_total $ uncons p >>= \case
    Left _ => emit False
    Right (vs,q) => case pred vs of
      False  => any pred q
      True   => emit True

||| Sums up the emitted chunks.
export %inline
sum : Num o => Pull f o es r -> Pull f o es r
sum = fold (+) 0

||| Counts the number of emitted chunks.
export %inline
count : Pull f o es r -> Pull f Nat es r
count = fold (const . S) 0

||| Emits the largest output encountered.
export %inline
maximum : Ord o => Pull f o es r -> Pull f o es r
maximum = fold1 max

||| Emits the smallest output encountered.
export %inline
minimum : Ord o => Pull f o es r -> Pull f o es r
minimum = fold1 min

||| Emits the smallest output encountered.
export %inline
mappend : Semigroup o => Pull f o es r -> Pull f o es r
mappend = fold1 (<+>)

||| Accumulates the emitted values over a monoid.
|||
||| Note: This corresponds to a left fold, so it will
|||       run in quadratic time for monoids that are
|||       naturally accumulated from the right (such as List)
export %inline
foldMap : Monoid m => (o -> m) -> Pull f o es r -> Pull f m es r
foldMap f = fold (\v,el => v <+> f el) neutral

||| Folds the emit of a pull using an initial value and binary operator.
|||
||| The accumulated result is emitted as a single value.
export
evalFold : (p -> o -> f es p) -> p -> Pull f o es r -> Pull f p es r
evalFold g v s =
  assert_total $ uncons s >>= \case
    Left res      => cons v (pure res)
    Right (vs,s2) => exec (g v vs) >>= \v2 => evalFold g v2 s2

||| Like `fold` but instead of emitting the result as a single
||| value of output, it is paired with the `Pull`s result.
export
evalFoldPair : (p -> o -> f es p) -> p -> Pull f o es r -> Pull f q es (p,r)
evalFoldPair g v s =
  assert_total $ uncons s >>= \case
    Left res      => pure (v, res)
    Right (vs,s2) => exec (g v vs) >>= \v2 => evalFoldPair g v2 s2

||| Convenience version of `evalFoldPair` for working on streams.
export %inline
evalFoldGet : (p -> o -> f es p) -> p -> Stream f es o -> Pull f q es p
evalFoldGet acc ini = map fst . evalFoldPair acc ini

--------------------------------------------------------------------------------
-- Scans
--------------------------------------------------------------------------------

||| Runs a stateful computation across all chunks of data.
export
scan : s -> (s -> o -> (p,s)) -> Pull f o es r -> Pull f p es r
scan s1 f p =
  assert_total $ uncons p >>= \case
    Left res    => pure res
    Right (v,q) => let (w,s2) := f s1 v in cons w (scan s2 f q)

||| General stateful conversion of a `Pull`s emit.
|||
||| Aborts as soon as the given accumulator function returns `Nothing`
export
scanMaybe : s -> (s -> Maybe (o -> (p,s))) -> Pull f o es r -> Pull f p es s
scanMaybe s1 f p =
  assert_total $ case f s1 of
    Nothing => pure s1
    Just g  => uncons p >>= \case
      Left _      => pure s1
      Right (v,p) => let (w,s2) := g v in cons w (scanMaybe s2 f p)

||| Like `scan` but will possibly also emit the final state.
export
scanFull :
     s
  -> (s -> o -> (Maybe p,s))
  -> (s -> Maybe p)
  -> Pull f o es r
  -> Pull f p es r
scanFull s1 g last p = do
  assert_total $ uncons p >>= \case
    Left v      => consMaybe (last s1) (pure v)
    Right (v,q) => let (w,s2) := g s1 v in consMaybe w (scanFull s2 g last q)

||| Zips the input with a running total, up to but
||| not including the current element.
export
zipWithScan : p -> (p -> o -> p) -> Pull f o es r -> Pull f (o,p) es r
zipWithScan vp fun =
  scan vp $ \vp1,vo => let vp2 := fun vp1 vo in ((vo, vp1),vp2)

||| Like `zipWithScan` but the running total is including the current element.
export
zipWithScan1 : p -> (p -> o -> p) -> Pull f o es r -> Pull f (o,p) es r
zipWithScan1 vp fun =
  scan vp $ \vp1,vo => let vp2 := fun vp1 vo in ((vo, vp2),vp2)

||| Pairs each element in the stream with its 0-based index.
export %inline
zipWithIndex : Pull f o es r -> Pull f (o,Nat) es r
zipWithIndex = zipWithScan 0 (\n,_ => S n)

||| Pairs each element in the stream with its 1-based count.
export %inline
zipWithCount : Pull f o es r -> Pull f (o,Nat) es r
zipWithCount = zipWithScan 1 (\n,_ => S n)

||| Accumulates the input value using the given function.
|||
||| The emitted result will include the input up to but
||| not including the current value.
export %inline
scans : p -> (p -> o -> p) -> Pull f o es r -> Pull f p es r
scans vp fun = scan vp $ \vp1,vo => let vp2 := fun vp1 vo in (vp1,vp2)

||| Like `scans` but the running total is including the current element.
export %inline
scans1 : p -> (p -> o -> p) -> Pull f o es r -> Pull f p es r
scans1 vp fun = scan vp $ \vp1,vo => let vp2 := fun vp1 vo in (vp2,vp2)

||| Emits the count of each element.
export %inline
runningCount : Pull f o es r -> Pull f Nat es r
runningCount = scan 1 (\n,_ => (n, S n))

||| Like `scan` but with an effectful computation.
export
evalScan : s -> (s -> o -> f es (p,s)) -> Pull f o es r -> Pull f p es r
evalScan s1 f p =
  assert_total $ uncons p >>= \case
    Left res    => pure res
    Right (v,q) => do
      (w,s2) <- exec $ f s1 v
      cons w (evalScan s2 f q)

parameters {0 es      : List Type}
           {0 f       : List Type -> Type -> Type}
           {auto func : Functor (f es)}
  ||| Accumulates the input value using the given function.
  |||
  ||| The emitted result will include the input up to but
  ||| not including the current value.
  export %inline
  evalScans : p -> (p -> o -> f es p) -> Pull f o es r -> Pull f p es r
  evalScans vp fun =
    evalScan vp $ \vp1,vo => (\vp2 => (vp1,vp2)) <$> fun vp1 vo

  ||| Like `scans` but the running total is including the current element.
  export %inline
  evalScans1 : p -> (p -> o -> f es p) -> Pull f o es r -> Pull f p es r
  evalScans1 vp fun =
    evalScan vp $ \vp1,vo => (\vp2 => (vp2,vp2)) <$> fun vp1 vo

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
flatMap : Pull f o es r -> (o -> Stream f es p) -> Pull f p es r
flatMap p g =
  assert_total $ uncons p >>= \case
    Left v       => pure v
    Right (os,q) => g os >> flatMap q g

||| Flipped version of `flatMapC`
export %inline
bind : (o -> Pull f p es ()) -> Pull f o es r -> Pull f p es r
bind = flip flatMap

export
attemptOutput : Pull f o es () -> Pull f (Result es o) fs ()
attemptOutput p =
  att (mapOutput Right p) >>= \case
    Left x  => emit (Left x)
    Right _ => pure ()
