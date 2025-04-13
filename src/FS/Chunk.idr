||| Utilities for working with chunks of data.
|||
||| It is suggested to import this qualified `import FS.Chunk as C` or
||| via the catch-all module `FS` and use qualified names such
||| as `C.filter` for those functions that overlap with the ones
||| from `FS.Pull`.
module FS.Chunk

import FS.Core as P
import FS.Pull as P
import Data.List
import Data.Maybe
import Data.Nat

%default total

--------------------------------------------------------------------------------
-- Chunk Size
--------------------------------------------------------------------------------

||| Pulls and streams produce their output in chunks (lists of value)
||| for reasons of efficiency, because the whole streaming machinery
||| comes with quite a bit of a performance overhead.
|||
||| Many functions for generating pure streams
||| and pulls therefore take an auto-implicit value of type `ChunkSize`.
||| If not provided explicitly, this defaults to 128.
public export
record ChunkSize where
  [noHints]
  constructor CS
  size        : Nat
  {auto 0 prf : IsSucc size}

export %inline
Eq ChunkSize where
  CS x == CS y = x == y

export %inline
Ord ChunkSize where
  compare (CS x) (CS y) = compare x y

export %inline
Show ChunkSize where
  show = show . size

export
fromInteger : (n : Integer) -> ChunkSize
fromInteger n =
  case cast {to = Nat} n of
    k@(S _) => CS k
    0       => CS 1

public export %inline %hint
defaultChunkSize : ChunkSize
defaultChunkSize = 128

--------------------------------------------------------------------------------
-- Chunk
--------------------------------------------------------------------------------

public export
data SplitRes : Type -> Type where
  Middle : (pre, post : c) -> SplitRes c
  All    : Nat -> SplitRes c

||| A `Chunk c o` is a container type `c` holding elements of type `o`.
|||
||| Examples include `List a` with element type `a` and `ByteString` with
||| element type `Bits8`.
public export
interface Monoid c => Chunk (0 c,o : Type) | c where
  unfoldChunk    : ChunkSize => (s ->  Either r (o,s)) -> s -> UnfoldRes r s c
  replicateChunk : ChunkSize => o -> c
  isEmpty        : c -> Bool
  unconsChunk    : c -> Maybe (o, Maybe c)
  splitChunkAt   : Nat -> c -> SplitRes c
  breakChunk     : BreakInstruction -> (o -> Bool) -> c -> BreakRes c
  filterChunk    : (o -> Bool) -> c -> Maybe c

export
nonEmpty : Chunk c o => c -> Maybe c
nonEmpty v = if isEmpty v then Nothing else Just v

--------------------------------------------------------------------------------
-- Creating streams of chunks
--------------------------------------------------------------------------------

||| Like `unfold` but generates chunks of values of up to the given size.
export %inline
unfold : ChunkSize => Chunk c o => s -> (s -> Either r (o,s)) -> Pull f c es r
unfold init g = P.unfold init (unfoldChunk g)

||| Like `P.fill` but generates chunks of values of up to the given size.
export
fill : ChunkSize => (0 c : _) -> Chunk c o => o -> Pull f c es ()
fill _ v = P.fill (replicateChunk v)

||| Like `P.iterate` but generates chunks of values of up to the given size.
export
iterate : ChunkSize => (0 c : _) -> Chunk c o => o -> (o -> o) -> Pull f c es ()
iterate _ v f = unfold v (\x => Right (x, f x))

||| Like `P.replicate` but generates chunks of values of up to the given size.
export
replicate : ChunkSize => (0 c : _) -> Chunk c o => Nat -> o -> Stream f es c
replicate _ n v =
  Chunk.unfold n $ \case
    0   => Left ()
    S k => Right (v,k)

--------------------------------------------------------------------------------
-- Splitting Streams
--------------------------------------------------------------------------------

parameters {auto chnk : Chunk c o}

  ||| Splits the very first element from the head of a `Pull`
  export
  uncons : Pull f c es r -> Pull f q es (Either r (o, Pull f c es r))
  uncons p =
    assert_total $ P.uncons p >>= \case
      Left x => pure (Left x)
      Right (vs,q) => case unconsChunk vs of
        Just (el,rem) => pure $ Right (el,consMaybe rem q)
        Nothing => Chunk.uncons q

  ||| Emits the first `n` elements of a `Pull`, returning the remainder.
  export
  splitAt : Nat -> Pull f c es r -> Pull f c es (Pull f c es r)
  splitAt 0 p = pure p
  splitAt k p =
    assert_total $ P.uncons p >>= \case
      Left v      => pure (pure v)
      Right (vs,q) => case splitChunkAt k vs of
        Middle pre post => cons pre (pure $ cons post q)
        All n           => cons vs (Chunk.splitAt n q)

  ||| Emits the first `n` elements of a `Pull`, returning the remainder.
  export %inline
  take : Nat -> Pull f c es r -> Pull f c es ()
  take 0 = const $ pure ()
  take n = ignore . newScope . Chunk.splitAt n

  ||| Like `take` but limits the number of emitted values.
  |||
  ||| This fails with the given error in case the limit is exceeded.
  export %inline
  limit : Has e es => Lazy e -> Nat -> Pull f c es r -> Pull f c es r
  limit err n p = do
    q      <- Chunk.splitAt n p
    Left v <- peekRes q | Right _ => throw err
    pure v

  ||| Drops the first `n` elements of a `Pull`, returning the
  ||| remainder.
  export %inline
  drop : Nat -> Pull f c es r -> Pull f c es r
  drop k p = join $ drain (Chunk.splitAt k p)

  ||| Emits the first element of a `Pull`, returning the remainder.
  export %inline
  head : Pull f c es r -> Pull f c es ()
  head = Chunk.take 1

  ||| Discards the first element of a `Pull`.
  export %inline
  tail : Pull f c es r -> Pull f c es r
  tail = Chunk.drop 1

  ||| Breaks a pull as soon as the given predicate returns `True` for
  ||| an emitted element.
  |||
  ||| `orElse` determines what to do if the pull is exhausted before any
  ||| splitting of output occurred.
  |||
  ||| The `BreakInstruction` dictates, if the value, for which the
  ||| predicate held, should be emitted as part of the prefix or the
  ||| suffix, or if it should be discarded.
  export
  breakFull :
       (orElse : r -> Pull f c es r)
    -> BreakInstruction
    -> (o -> Bool)
    -> Pull f c es r
    -> Pull f c es (Pull f c es r)
  breakFull orElse bi pred = breakPull orElse (breakChunk bi pred)

  ||| Like `breakFull` but fails with an error if the `Pull` is
  ||| exhausted before the prediate returns `True`.
  export %inline
  forceBreakFull :
       {auto has : Has e es}
    -> Lazy e
    -> BreakInstruction
    -> (o -> Bool)
    -> Pull f c es r
    -> Pull f c es (Pull f c es r)
  forceBreakFull err = breakFull (const $ throw err)

  ||| Emits values until the given predicate returns `True`.
  |||
  ||| The `BreakInstruction` dictates, if the value, for which the
  ||| predicate held, should be emitted as part of the prefix or not.
  export
  takeUntil : BreakInstruction -> (o -> Bool) -> Pull f c es r -> Stream f es c
  takeUntil tf pred = ignore . newScope . Chunk.breakFull pure tf pred

  ||| Emits values until the given predicate returns `False`,
  ||| returning the remainder of the `Pull`.
  export %inline
  takeWhile : (o -> Bool) -> Pull f c es r -> Stream f es c
  takeWhile pred = Chunk.takeUntil DropHit (not . pred)

  ||| Like `takeWhile` but also includes the first failure.
  export %inline
  takeThrough : (o -> Bool) -> Pull f c es r -> Stream f es c
  takeThrough pred = Chunk.takeUntil TakeHit (not . pred)

  ||| Discards values until the given predicate returns `True`.
  |||
  ||| The `BreakInstruction` dictates, if the value, for which the
  ||| predicate held, should be emitted as part of the remainder or not.
  export
  dropUntil : BreakInstruction -> (o -> Bool) -> Pull f c es r -> Pull f c es r
  dropUntil tf pred p = drain (Chunk.breakFull pure tf pred p) >>= id

  ||| Drops values from a stream while the given predicate returns `True`,
  ||| returning the remainder of the stream.
  export %inline
  dropWhile : (o -> Bool) -> Pull f c es r -> Pull f c es r
  dropWhile pred = Chunk.dropUntil PostHit (not . pred)

  ||| Like `dropWhile` but also drops the first value where
  ||| the predicate returns `False`.
  export %inline
  dropThrough : (o -> Bool) -> Pull f c es r -> Pull f c es r
  dropThrough pred = Chunk.dropUntil DropHit (not . pred)

  ||| Splits a stream of chunks whenever an element fulfills the given
  ||| predicate.
  export
  split : (o -> Bool) -> Pull f c es r -> Pull f (List c)  es r
  split pred = scanFull neutral impl (map pure . nonEmpty)
    where
      loop : SnocList c -> Maybe c -> (Maybe $ List c, c)
      loop sc Nothing  = (Just $ sc <>> [], neutral)
      loop sc (Just x) =
        assert_total $ case breakChunk DropHit pred x of
          Broken x post => loop (sc :< fromMaybe neutral x) post
          Keep x        => (Just $ sc <>> [], x)

      impl : c -> c -> (Maybe $ List c, c)
      impl pre cur =
        case breakChunk DropHit pred cur of
          Broken x post => loop [<pre <+> fromMaybe neutral x] post
          Keep x        => (Nothing, pre <+> x)

--------------------------------------------------------------------------------
-- Maps and Filters
--------------------------------------------------------------------------------

nel : List a -> Maybe (List a)
nel [] = Nothing
nel xs = Just xs

||| Maps elements of output via a partial function.
export
mapMaybe : (o -> Maybe p) -> Pull f (List o) es r -> Pull f (List p) es r
mapMaybe f = P.mapMaybe (nel . mapMaybe f)

||| Element-wise filtering of a stream of chunks.
export %inline
filter : Chunk c o => (o -> Bool) -> Pull f c es r -> Pull f c es r
filter = P.mapMaybe . filterChunk

||| Element-wise filtering of a stream of chunks.
export %inline
filterNot : Chunk c o => (o -> Bool) -> Pull f c es r -> Pull f c es r
filterNot pred = Chunk.filter (not . pred)

||| Maps a function over all elements emitted by a pull.
export %inline
mapOutput : Functor t => (o -> p) -> Pull f (t o) es r -> Pull f (t p) es r
mapOutput = P.mapOutput . map

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

parameters {auto fld : Foldable t}

  export %inline
  fold : (p -> o -> p) -> p -> Pull f (t o) es r -> Pull f p es r
  fold g = P.fold (foldl g)

  ||| Like `fold` but instead of emitting the result as a single
  ||| value of output, it is paired with the `Pull`s result.
  export %inline
  foldPair : (p -> o -> p) -> p -> Pull f (t o) es r -> Pull f q es (p,r)
  foldPair g = P.foldPair (foldl g)

  ||| Convenience version of `foldPair` for working on streams.
  export %inline
  foldGet : (p -> o -> p) -> p -> Stream f es (t o) -> Pull f q es p
  foldGet g = P.foldGet (foldl g)

  ||| Like `foldC` but will not emit a value in case of an empty pull.
  export
  fold1 : Chunk (t o) o => (o -> o -> o) -> Pull f (t o) es r -> Pull f o es r
  fold1 g s =
    Chunk.uncons s >>= \case
      Left r      => pure r
      Right (v,q) => Chunk.fold g v q

  ||| Returns `True` if all emitted values of the given stream fulfill
  ||| the given predicate
  export %inline
  all : (o -> Bool) -> Pull f (t o) es r -> Stream f es Bool
  all pred = P.all (all pred)

  ||| Returns `True` if any of the emitted values of the given stream fulfills
  ||| the given predicate
  export %inline
  any : (o -> Bool) -> Pull f (t o) es r -> Stream f es Bool
  any pred = P.any (any pred)

  ||| Emits the sum over all elements emitted by a `Pull`.
  export %inline
  sum : Num o => Pull f (t o) es r -> Pull f o es r
  sum = Chunk.fold (+) 0

  ||| Emits the number of elements emitted by a `Pull`.
  export %inline
  count : Pull f (t o) es r -> Pull f Nat es r
  count = Chunk.fold (const . S) 0

  ||| Emits the largest output encountered.
  export %inline
  maximum : Chunk (t o) o => Ord o => Pull f (t o) es r -> Pull f o es r
  maximum = Chunk.fold1 max

  ||| Emits the smallest output encountered.
  export %inline
  minimum : Chunk (t o) o => Ord o => Pull f (t o) es r -> Pull f o es r
  minimum = Chunk.fold1 min

  ||| Emits the smallest output encountered.
  export %inline
  mappend : Chunk (t o) o => Semigroup o => Pull f (t o) es r -> Pull f o es r
  mappend = Chunk.fold1 (<+>)

  ||| Accumulates the emitted values over a monoid.
  |||
  ||| Note: This corresponds to a left fold, so it will
  |||       run in quadratic time for monoids that are
  |||       naturally accumulated from the right (such as List)
  export %inline
  foldMap : Monoid m => (o -> m) -> Pull f (t o) es r -> Pull f m es r
  foldMap f = Chunk.fold (\v,el => v <+> f el) neutral

--------------------------------------------------------------------------------
-- Scans
--------------------------------------------------------------------------------

public export
interface Functor f => Scan f where
  scanChunk : (s -> o -> (p,s)) -> s -> f o -> (f p, s)

parameters {auto sca : Scan t}

  ||| Computes a stateful running total over all elements emitted by a
  ||| pull.
  export %inline
  scan : s -> (s -> o -> (p,s)) -> Pull f (t o) es r -> Pull f (t p) es r
  scan ini f = P.scan ini (scanChunk f)

  ||| Zips the input with a running total according to `s`, up to but
  ||| not including the current element. Thus the initial
  ||| `vp` value is the first emitted to the output:
  export
  zipWithScan : p -> (p -> o -> p) -> Pull f (t o) es r -> Pull f (t (o,p)) es r
  zipWithScan vp fun =
    Chunk.scan vp $ \vp1,vo => let vp2 := fun vp1 vo in ((vo, vp1),vp2)

  ||| Like `zipWithScan` but the running total is including the current element.
  export
  zipWithScan1 : p -> (p -> o -> p) -> Pull f (t o) es r -> Pull f (t (o,p)) es r
  zipWithScan1 vp fun =
    Chunk.scan vp $ \vp1,vo => let vp2 := fun vp1 vo in ((vo, vp2),vp2)

  ||| Pairs each element in the stream with its 0-based index.
  export %inline
  zipWithIndex : Pull f (t o) es r -> Pull f (t (o,Nat)) es r
  zipWithIndex = Chunk.zipWithScan 0 (\n,_ => S n)

  ||| Pairs each element in the stream with its 1-based count.
  export %inline
  zipWithCount : Pull f (t o) es r -> Pull f (t (o,Nat)) es r
  zipWithCount = Chunk.zipWithScan 1 (\n,_ => S n)

  ||| Emits the count of each element.
  export %inline
  runningCount : Pull f (t o) es r -> Pull f (t Nat) es r
  runningCount = Chunk.scan 1 (\n,_ => (n, S n))

--------------------------------------------------------------------------------
-- List Implementation
--------------------------------------------------------------------------------

%inline
len : SnocList a -> Maybe (List a)
len = nel . (<>> [])

broken : SnocList a -> List a -> BreakRes (List a)
broken sx xs = Broken (len sx) (nel xs)

unfoldList :
     SnocList o
  -> Nat
  -> (s -> Either r (o,s))
  -> s
  -> UnfoldRes r s (List o)
unfoldList sx 0     f x = More (sx <>> []) x
unfoldList sx (S k) f x =
  case f x of
    Right (v,x2) => unfoldList (sx:<v) k f x2
    Left res     => Last res (sx <>> [])

splitAtList : SnocList o -> Nat -> List o -> SplitRes (List o)
splitAtList sx (S k) (h::t) = splitAtList (sx :< h) k t
splitAtList sx n     []     = All n
splitAtList sx 0     xs     = Middle (sx <>> []) xs

breakList :
     SnocList a
  -> BreakInstruction
  -> (a -> Bool)
  -> List a
  -> BreakRes (List a)
breakList sx b f []        = Keep (sx <>> [])
breakList sx b f (x :: xs) =
  case f x of
    True => case b of
      TakeHit => broken (sx :< x) xs
      PostHit => broken sx (x::xs)
      DropHit => broken sx xs
    False => breakList (sx :< x) b f xs

export
Chunk (List a) a where
  unfoldChunk @{CS (S n)} f x =
    case f x of
      Left res     => Done res
      Right (v,x2) => unfoldList [<v] n f x2

  replicateChunk @{CS n} = List.replicate n

  isEmpty [] = True
  isEmpty _  = False

  unconsChunk []     = Nothing
  unconsChunk (h::t) = Just (h, nel t)

  splitChunkAt = splitAtList [<]

  breakChunk = breakList [<]

  filterChunk pred = nel . filter pred

scanListImpl : SnocList p -> (s -> o -> (p,s)) -> s -> List o -> (List p,s)
scanListImpl sx f v []        = (sx <>> [], v)
scanListImpl sx f v (x :: xs) =
  let (vp,v2) := f v x
  in scanListImpl (sx :< vp) f v2 xs

export
Scan List where
  scanChunk = scanListImpl [<]

--------------------------------------------------------------------------------
-- Zipping
--------------------------------------------------------------------------------
--
-- public export
-- data ZipRes : (a,b,c : Type) -> Type where
--   Z  : List c -> ZipRes a b c
--   ZL : List a -> List c -> ZipRes a b c
--   ZR : List b -> List c -> ZipRes a b c
--
-- export
-- zipImpl : SnocList c -> (a -> b -> c) -> List a -> List b -> ZipRes a b c
-- zipImpl sx f (x::xs) (y::ys) = zipImpl (sx :< f x y) f xs ys
-- zipImpl sx f [] [] = Z (sx <>> [])
-- zipImpl sx f xs [] = ZL xs (sx <>> [])
-- zipImpl sx f [] ys = ZR ys (sx <>> [])
