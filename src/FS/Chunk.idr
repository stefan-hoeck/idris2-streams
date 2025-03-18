||| Utilities for working with chunks of data.
module FS.Chunk

import FS.Pull
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
  unfoldChunk : ChunkSize => (s ->  Either r (o,s)) -> s -> UnfoldRes r s c
  isEmpty      : c -> Bool
  unconsChunk  : c -> Maybe (o, c)
  splitChunkAt : Nat -> c -> SplitRes c
  breakChunk   : (keepHit : Bool) -> (o -> Bool) -> c -> BreakRes c

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

||| Like `unfold` but generates chunks of values of up to the given size.
export %inline
unfoldEl : ChunkSize => Chunk c o => s -> (s -> Either r (o,s)) -> Pull f c es r
unfoldEl init g = unfold init (unfoldChunk g)

||| Like `fill` but generates chunks of values of up to the given size.
export
fillEl : ChunkSize => Chunk c o => o -> Pull f c es ()
fillEl v =
  let chunk := unfoldChunk (\_ => Right (v,())) ()
   in unfold () (const chunk)

||| Like `iterate` but generates chunks of values of up to the given size.
export
iterateEl : ChunkSize => Chunk c o => o -> (o -> o) -> Stream f es c
iterateEl v f = unfoldEl v (\x => Right (x, f x))

||| Like `replicate` but generates chunks of values of up to the given size.
export
replicateEl : ChunkSize => Chunk c o => Nat -> o -> Stream f es c
replicateEl n v =
  unfoldEl n $ \case
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
breakEl : Chunk c o => (o -> Bool) -> Pull f c es r -> Pull f c es (Pull f c es r)
breakEl = breakPull . breakChunk False

-- ||| Emits the first `n` elements of a `Pull`, returning the remainder.
-- export
-- takeEl : Split o => Nat -> Pull f o es r -> Pull f o es (Pull f o es r)
-- takeEl k p =
--   assert_total $ uncons p >>= \case
--     Left v      => pure (pure v)
--     Right (vs,q) => case splitAt k vs of
--       Middle pre post => emit pre $> cons post q
--       All pre n       => emit pre >> takeEl n q
--       Naught          => pure (cons vs q)
--
-- ||| Drops the first `n` values of a `Pull`, returning the
-- ||| remainder.
-- export
-- dropEl : Split o => Nat -> Pull f o es r -> Pull f o es r
-- dropEl k p =
--   assert_total $ uncons p >>= \case
--     Left v      => pure v
--     Right (vs,q) => case splitAt k vs of
--       Middle pre post => cons post q
--       All _ n         => dropEl n q
--       Naught          => q
--

-- ||| Perform the given action on every emitted value.
-- |||
-- ||| For acting on output without actually draining the stream, see
-- ||| `observe` and `observe1`.
-- export
-- foreach1 : Uncons c o => (o -> f es ()) -> Pull f c es r -> Pull f q es r
-- foreach1 f p =
--   assert_total $ unconsEl p >>= \case
--     Left x      => pure x
--     Right (v,p) => exec (f v) >> foreach1 f p

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
breakList sx b f []        = None
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

  isEmpty [] = True
  isEmpty _  = False

  unconsChunk []     = Nothing
  unconsChunk (h::t) = Just (h,t)

  splitChunkAt 0 _  = Naught
  splitChunkAt n xs = splitAtList [<] n xs

  breakChunk = breakList [<]

-- --------------------------------------------------------------------------------
-- -- Break
-- --------------------------------------------------------------------------------
--

-- ||| Used for implementing `FS.Pull.takeWhile` and `FS.Pull.takeThrough`
-- export
-- takeWhileImpl : Bool -> SnocList o -> (o -> Bool) -> List o -> Maybe (List o,List o)
-- takeWhileImpl tf sx f []        = Nothing
-- takeWhileImpl tf sx f (x :: xs) =
--   if      f x then takeWhileImpl tf (sx :< x) f xs
--   else if tf  then Just (sx <>> [x], xs)
--   else             Just (sx <>> [], x::xs)
--
-- ||| Used for implementing `FS.Pull.takeWhileJust`
-- export
-- takeWhileJustImpl : SnocList o -> List (Maybe o) -> (List o,List $ Maybe o)
-- takeWhileJustImpl sx []        = (sx <>> [], [])
-- takeWhileJustImpl sx (x :: xs) =
--   case x of
--     Nothing => (sx <>> [], Nothing :: xs)
--     Just v  => takeWhileJustImpl (sx :< v) xs
--
-- ||| Used for implementing `FS.Pull.dropWhile` and `FS.Pull.dropThrough`
-- export
-- dropWhileImpl : (o -> Bool) -> List o -> List o
-- dropWhileImpl f []        = []
-- dropWhileImpl f (x :: xs) = if f x then dropWhileImpl f xs else x::xs
--
-- ||| Used for implementing `FS.Pull.find`
-- export
-- findImpl : (o -> Bool) -> List o -> Maybe (o,List o)
-- findImpl f []        = Nothing
-- findImpl f (x :: xs) = if f x then Just (x,xs) else findImpl f xs
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
