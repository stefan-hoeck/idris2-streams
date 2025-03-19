||| Utilities for working with chunks of data.
module FS.Chunk

import FS.Pull
import Data.List
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
  Naught : SplitRes c
  All    : Nat -> SplitRes c

||| A `Chunk c o` is a container type `c` holding elements of type `o`.
|||
||| Examples include `List a` with element type `a` and `ByteString` with
||| element type `Bits8`.
public export
interface Chunk (0 c,o : Type) | c where
  unfoldChunk    : ChunkSize => (s ->  Either r (o,s)) -> s -> UnfoldRes r s c
  replicateChunk : ChunkSize => o -> c
  isEmpty        : c -> Bool
  unconsChunk    : c -> Maybe (o, c)
  splitChunkAt   : Nat -> c -> SplitRes c
  breakChunk     : (keepHit : Bool) -> (o -> Bool) -> c -> BreakRes c
  filterChunk    : (o -> Bool) -> c -> c

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Like `unfold` but generates chunks of values of up to the given size.
export %inline
unfold : ChunkSize => Chunk c o => s -> (s -> Either r (o,s)) -> Pull f c es r
unfold init g = unfoldC init (unfoldChunk g)

||| Like `fill` but generates chunks of values of up to the given size.
export
fill : ChunkSize => Chunk c o => o -> Pull f c es ()
fill v = fillC (replicateChunk v)

||| Like `iterate` but generates chunks of values of up to the given size.
export
iterate : ChunkSize => Chunk c o => o -> (o -> o) -> Stream f es c
iterate v f = unfold v (\x => Right (x, f x))

||| Like `replicate` but generates chunks of values of up to the given size.
export
replicate : ChunkSize => Chunk c o => Nat -> o -> Stream f es c
replicate n v =
  unfold n $ \case
    0   => Left ()
    S k => Right (v,k)

export
consChunk : Chunk c o => c -> Pull f c es r -> Pull f c es r
consChunk x p = if isEmpty x then p else cons x p

||| Splits the very value from the head of a `Pull`
export
unconsEl : Chunk c o => Pull f c es r -> Pull f q es (Either r (o, Pull f c es r))
unconsEl p =
  assert_total $ uncons p >>= \case
    Left x => pure (Left x)
    Right (vs,q) => case unconsChunk vs of
      Just (el,rem) => pure $ Right (el,consChunk rem q)
      Nothing => unconsEl q

||| Breaks the stream at the first element that returns `True`.
|||
||| The element that returned `True` will be the first element of
||| the remainder.
export %inline
break : Chunk c o => (o -> Bool) -> Pull f c es r -> Pull f c es (Pull f c es r)

||| Emits elements until the given predicate returns `False`.
export %inline
takeWhile : Chunk c o => (o -> Bool) -> Stream f es c -> Stream f es c
takeWhile pred = ignore . break (not . pred)

||| Emits the first `n` elements of a `Pull`, returning the remainder.
export
take : Chunk c o => Nat -> Pull f c es r -> Pull f c es (Pull f c es r)
take k p =
  assert_total $ uncons p >>= \case
    Left v      => pure (pure v)
    Right (vs,q) => case splitChunkAt k vs of
      Middle pre post => emit pre $> cons post q
      All n           => emit vs >> take n q
      Naught          => pure (cons vs q)

||| Drops the first `n` elements of a `Pull`, returning the
||| remainder.
export
drop : Chunk c o => Nat -> Pull f c es r -> Pull f c es r
drop k p =
  assert_total $ uncons p >>= \case
    Left v      => pure v
    Right (vs,q) => case splitChunkAt k vs of
      Middle pre post => cons post q
      All n           => drop n q
      Naught          => q

||| Perform the given action on every emitted value.
|||
||| For acting on output without actually draining the stream, see
||| `observe` and `observe1`.
export
foreachEl : Chunk c o => (o -> f es ()) -> Pull f c es r -> Pull f q es r
foreachEl f p =
  assert_total $ unconsEl p >>= \case
    Left x      => pure x
    Right (v,p) => exec (f v) >> foreachEl f p

--------------------------------------------------------------------------------
-- Maps and Filters
--------------------------------------------------------------------------------

||| Element-wise filtering of a stream of chunks.
export
filter : Chunk c o => (o -> Bool) -> Pull f c es r -> Pull f c es r
filter pred =
  mapMaybeC $ \v =>
   let w := filterChunk pred v
    in if isEmpty w then Nothing else Just w

||| Element-wise filtering of a stream of chunks.
export %inline
filterNot : Chunk c o => (o -> Bool) -> Pull f c es r -> Pull f c es r
filterNot pred = filter (not . pred)

||| Maps a function over all elements emitted by a pull.
export %inline
mapEl : Functor t => (o -> p) -> Pull f (t o) es r -> Pull f (t p) es r
mapEl = mapC . map

||| Maps a partial function over all elements emitted by a pull.
export %inline
mapMaybe : (o -> Maybe p) -> Pull f (List o) es r -> Pull f (List p) es r
mapMaybe f =
  mapMaybeC $ \vs => case mapMaybe f vs of
    [] => Nothing
    ws => Just ws

--------------------------------------------------------------------------------
-- Folds
--------------------------------------------------------------------------------

export %inline
fold : Foldable t => (p -> o -> p) -> p -> Pull f (t o) es r -> Pull f p es r
fold g = foldC (foldl g)

||| Returns `True` if all emitted values of the given stream fulfill
||| the given predicate
export %inline
all : Foldable t => (o -> Bool) -> Stream f es (t o) -> Stream f es Bool
all pred = allC (all pred)

||| Returns `True` if any of the emitted values of the given stream fulfills
||| the given predicate
export %inline
any : Foldable t => (o -> Bool) -> Stream f es (t o) -> Stream f es Bool
any pred = anyC (any pred)

||| Emits the sum over all elements emitted by a `Pull`.
export %inline
sum : Foldable t => Num o => Pull f (t o) es r -> Pull f o es r
sum = fold (+) 0

||| Emits the number of elements emitted by a `Pull`.
export %inline
count : Foldable t => Pull f (t o) es r -> Pull f Nat es r
count = fold (const . S) 0

--------------------------------------------------------------------------------
-- Scans
--------------------------------------------------------------------------------

||| Computes a stateful running total over all elements emitted by a
||| pull.
export
scan : st -> (st -> o -> (p,st)) -> Pull f (List o) es r -> Pull f (List p) es r
scan ini f = scanC ini (go [<])
  where
    go : SnocList p -> st -> List o -> (List p, st)
    go sx cur []        = (sx <>> [], cur)
    go sx cur (x :: xs) = let (y,c2) := f cur x in go (sx:<y) c2 xs

||| Zips the input with a running total according to `s`, up to but
||| not including the current element. Thus the initial
||| `vp` value is the first emitted to the output:
export
zipWithScan :
     p
  -> (p -> o -> p)
  -> Pull f (List o) es r
  -> Pull f (List (o,p)) es r
zipWithScan vp fun =
  scan vp $ \vp1,vo => let vp2 := fun vp1 vo in ((vo, vp1),vp2)

||| Pairs each element in the stream with its 0-based index.
export %inline
zipWithIndex : Pull f (List o) es r -> Pull f (List (o,Nat)) es r
zipWithIndex = zipWithScan 0 (\n,_ => S n)

||| Like `zipWithScan` but the running total is including the current element.
export
zipWithScan1 : p -> (p -> o -> p) -> Stream f es o -> Stream f es (o,p)
-- zipWithScan1 vp fun =
--   mapAccumulate vp $ \vp1,vo =>
--     let vp2 := fun vp1 vo
--      in (vp2, (vo, vp2))

--------------------------------------------------------------------------------
-- List Implementation
--------------------------------------------------------------------------------

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

breakList : SnocList a -> Bool -> (a -> Bool) -> List a -> BreakRes (List a)
breakList sx b f []        = Keep (sx <>> [])
breakList sx b f (x :: xs) =
  case f x of
    True => case b of
      True  => case xs of
        []  => NoPost (sx <>> [x])
        _   => Broken (sx <>> [x]) xs
      False => case sx of
        [<] => NoPre (x::xs)
        _   => Broken (sx <>> []) (x::xs)
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
  unconsChunk (h::t) = Just (h,t)

  splitChunkAt 0 _  = Naught
  splitChunkAt n xs = splitAtList [<] n xs

  breakChunk = breakList [<]

  filterChunk = filter

-- --------------------------------------------------------------------------------
-- -- Break
-- --------------------------------------------------------------------------------
--
--
-- chunkedGo :
--      SnocList (List a)
--   -> SnocList a
--   -> Nat
--   -> Nat
--   -> List a
--   -> List (List a)
-- chunkedGo sxs sx _  _     []     = sxs <>> [sx <>> []]
-- chunkedGo sxs sx sz 0     (h::t) = chunkedGo (sxs :< (sx <>> [])) [<h] sz sz t
-- chunkedGo sxs sx sz (S m) (h::t) = chunkedGo sxs (sx:<h) sz m t
--
-- ||| Groups a list of values into chunks of size `n`.
-- |||
-- ||| Only the last list might be shorter.
-- export
-- chunked : (n : Nat) -> (0 p : IsSucc n) => List a -> List (List a)
-- chunked _      []     = []
-- chunked (S sz) (h::t) = chunkedGo [<] [<h] sz sz t
--
-- export
-- mapAccum : SnocList p -> (s -> o -> (s,p)) -> s -> List o -> (List p,s)
-- mapAccum sx f s1 []        = (sx <>> [], s1)
-- mapAccum sx f s1 (x :: xs) =
--   let (s2,vp) := f s1 x
--    in mapAccum (sx :< vp) f s2 xs
--
-- --------------------------------------------------------------------------------
-- -- Zipping
-- --------------------------------------------------------------------------------
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
