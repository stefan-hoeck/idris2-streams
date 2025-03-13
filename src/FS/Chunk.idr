||| Utilities for working with chunks of data.
module FS.Chunk

import Data.ByteVect
import Data.Array
import public Data.Nat

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
data Chunk : Type -> Type where
  Lst   : List a -> Chunk a
  Bytes : (sz : Nat) -> ByteVect sz -> Chunk Bits8

export
Functor Chunk where
  map f (Lst vs)      = Lst $ map f vs
  map f (Bytes sz bv) = Lst $ map f (unpack bv)

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

-- ||| Utility for implementing `FS.Pull.unfold`
-- export
-- unfoldImpl :
--      SnocList o
--   -> Nat
--   -> (s -> Either r (o,s))
--   -> s
--   -> (List o, Either r s)
-- unfoldImpl sx 0     f x = (sx <>> [], Right x)
-- unfoldImpl sx (S k) f x =
--   case f x of
--     Right (v,x2) => unfoldImpl (sx:<v) k f x2
--     Left res     => (sx <>> [], Left res)
--
-- ||| Utility for implementing `FS.Pull.unfoldMaybe`
-- export
-- unfoldMaybeImpl :
--      SnocList o
--   -> Nat
--   -> (s -> Maybe (o,s))
--   -> s
--   -> (List o, Maybe s)
-- unfoldMaybeImpl sx 0     f x = (sx <>> [], Just x)
-- unfoldMaybeImpl sx (S k) f x =
--   case f x of
--     Just (v,x2) => unfoldMaybeImpl (sx:<v) k f x2
--     Nothing     => (sx <>> [], Nothing)
--
-- ||| Utility for implementing `FS.Pull.iterate`
-- export
-- iterateImpl : SnocList o -> Nat -> (o -> o) -> o -> (List o, Maybe o)
-- iterateImpl sx 0     f x = (sx <>> [], Just x)
-- iterateImpl sx (S k) f x = iterateImpl (sx :< x) k f (f x)
--
-- ||| Stack-safe implementation of `splitAt`
-- export
-- splitAtImpl : SnocList a -> List a -> Nat -> (List a, List a)
-- splitAtImpl sv (v::vs) (S k) = splitAtImpl (sv:<v) vs k
-- splitAtImpl sv vs      _     = (sv <>> [], vs)
--
-- ||| Used for implementing `FS.Pull.take`
-- export
-- takeImpl : SnocList o -> Nat -> List o -> (Nat, List o, List o)
-- takeImpl sx (S k) (x :: xs) = takeImpl (sx :< x) k xs
-- takeImpl sx k     xs        = (k, sx <>> [], xs)
--
-- ||| Used for implementing `FS.Pull.drop`
-- export
-- dropImpl : Nat -> List o -> (Nat, List o)
-- dropImpl (S k) (x :: xs) = dropImpl k xs
-- dropImpl k     xs        = (k, xs)
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
