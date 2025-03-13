||| Utilities for working with chunks of data.
module FS.Chunk

import Data.Array.Core
import Data.Array.Mutable
import FS.Internal.IChunk
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
  Empty : Chunk a
  Chnk  : (len : Nat) -> (0 p : IsSucc len) => IChunk len a -> Chunk a

public export
size : Chunk a -> Nat
size Empty      = 0
size (Chnk l _) = l

--------------------------------------------------------------------------------
-- Making Chunks
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Chunk Concatenation
--------------------------------------------------------------------------------

||| Size of the chunk after concatenating a SnocList of chunks.
public export
SnocSize : SnocList (Chunk a) -> Nat
SnocSize [<]       = 0
SnocSize (xs :< x) = SnocSize xs + size x

public export
ListSize : List (Chunk a) -> Nat
ListSize = SnocSize . ([<] <><)

-- snocConcat implementation
sconc :
     (pos         : Nat)
  -> (cur         : Nat)
  -> (x           : IChunk m a)
  -> (arrs        : SnocList (Chunk a))
  -> {auto 0 lte1 : LTE pos n}
  -> {auto 0 lte2 : LTE cur m}
  -> WithMArray n a (IChunk n a)
sconc pos   0    _   (sx :< Chnk s x) r t = sconc pos s x   sx r t
sconc pos   0    arr (sx :< Empty)    r t = sconc pos 0 arr sx r t
sconc (S j) (S k) x   sx            r t =
  let _ # t := setNat r j (atNat x k) t
   in sconc j k x sx r t
sconc _     _     _   _             r t =
  let res # t := unsafeFreeze r t
   in Arr 0 reflexive res # t

-- ||| Concatenate a SnocList of arrays.
-- |||
-- ||| This allocates a large enough array in advance, and therefore runs in
-- ||| O(SnocSize sa).
-- export
-- snocConcat : (sa : SnocList (Chunk a)) -> IArray (SnocSize sa) a
-- snocConcat [<]                 = empty
-- snocConcat (sa :< A 0 _)       =
--   rewrite plusZeroRightNeutral (SnocSize sa) in snocConcat sa
-- snocConcat (sa :< A (S k) arr) with (SnocSize sa + S k)
--   _ | n = alloc n (at arr 0) (sconc n (S k) arr sa)
--
-- ||| Concatenate a List of arrays.
-- |||
-- ||| This allocates a large enough array in advance, and therefore runs in
-- ||| O(ListSize as).
-- export
-- listConcat : (as : List (Chunk a)) -> IArray (ListSize as) a
-- listConcat as = snocConcat ([<] <>< as)
--
-- ||| Concatenate two arrays in O(m+n) runtime.
-- export
-- append : {m,n : Nat} -> IArray m a -> IArray n a -> IArray (m + n) a
-- append xs ys = snocConcat [<A m xs, A n ys]

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export
Eq a => Eq (Chunk a) where
  Empty      == Empty = True
  Chnk l1 c1 == Chnk l2 c2 = heq c1 c2
  _          == _ = False

export
Ord a => Ord (Chunk a) where
  compare Empty Empty = EQ
  compare (Chnk l1 c1) (Chnk l2 c2) = hcomp c1 c2
  compare Empty _ = LT
  compare _ Empty = GT

export
Functor Chunk where
  map f Empty = Empty
  map f (Chnk n vs) = Chnk n $ map f vs

export
Foldable Chunk where
  foldl f i Empty = i
  foldl f i (Chnk _ vs) = foldl f i vs

  foldr f i Empty = i
  foldr f i (Chnk _ vs) = foldr f i vs

  foldMap f Empty = neutral
  foldMap f (Chnk _ vs) = foldMap f vs

  toList Empty = []
  toList (Chnk _ vs) = toList vs

  null Empty = True
  null _ = False
--
-- export
-- Semigroup (Chunk a) where
--   Bts xs <+> Bts ys = Bts $ xs <+> ys
--   xs     <+> ys     =
--     if      null xs then ys
--     else if null ys then xs
--     else Lst (toList xs ++ toList ys)
--
-- export
-- Monoid (Chunk a) where
--   neutral = Lst []

export %inline
singleton : a -> Chunk a
singleton v = Chnk 1 (fill 1 v)
--
-- export %inline
-- fromList : List a -> Chunk a
-- fromList = Lst
--
-- export %inline
-- fromSnoc : SnocList a -> Chunk a
-- fromSnoc = Lst . (<>> [])
--
-- export %inline
-- Cast (List a) (Chunk a) where cast = Lst
--
-- export %inline
-- Cast (SnocList a) (Chunk a) where cast = Lst . (<>> [])
--
-- export %inline
-- Cast ByteString (Chunk Bits8) where cast = Bts
--
-- export
-- uncons : Chunk a -> Maybe (a, Chunk a)
-- uncons (Lst (h::t))        = Just (h, Lst t)
-- uncons (Bts $ BS (S k) bv) = Just (head bv, Bts (BS k $ tail bv))
-- uncons _                   = Nothing
--
-- export
-- Eq a => Eq (Chunk a) where
--   Bts xs == Bts ys = xs == ys
--   xs     == ys     = toList xs == toList ys
--
-- export
-- Show a => Show (Chunk a) where
--   showPrec p xs = showCon p "fromList " (show $ toList xs)
--
-- export %inline
-- bytes : ByteString -> Chunk Bits8
-- bytes = Bts
--
-- concBytes : SnocList ByteString -> List (Chunk Bits8) -> Chunk Bits8
-- concBytes sx []      = Bts (fastConcat $ sx <>> [])
-- concBytes sx (x::xs) =
--   case x of
--     Bts (BS 0 _) => concBytes sx xs
--     Bts bs       => concBytes (sx:<bs) xs
--     Lst []       => concBytes sx xs
--     Lst vs       => concBytes (sx :< pack vs) xs
--
-- concLists : SnocList a -> List (Chunk a) -> Chunk a
-- concLists sx []        = cast sx
-- concLists sx (x :: xs) =
--   case x of
--     Lst []       => concLists sx xs
--     Lst vs       => concLists (sx <>< vs) xs
--     Bts (BS 0 _) => concBytes [< pack $ sx <>> []] xs
--     Bts bs       => concBytes [< pack $ sx <>> [], bs] xs
--
-- export
-- fastConcat : List (Chunk a) -> Chunk a
-- fastConcat = concLists [<]
--
-- --------------------------------------------------------------------------------
-- -- Utilities
-- --------------------------------------------------------------------------------
--
-- export
-- filter : (a -> Bool) -> Chunk a -> Chunk a
-- filter pred (Lst vs) = Lst $ filter pred vs
-- filter pred (Bts bs) = Bts $ filter pred bs
--
-- export
-- mapMaybe : (a -> Maybe b) -> Chunk a -> Chunk b
-- mapMaybe f = fromList . mapMaybe f . toList
--
-- ||| Utility for implementing `FS.Pull.unfold`
-- export
-- unfoldImpl :
--      SnocList o
--   -> Nat
--   -> (s -> Either r (o,s))
--   -> s
--   -> (Chunk o, Either r s)
-- unfoldImpl sx 0     f x = (cast sx, Right x)
-- unfoldImpl sx (S k) f x =
--   case f x of
--     Right (v,x2) => unfoldImpl (sx:<v) k f x2
--     Left res     => (cast sx, Left res)
--
-- ||| Utility for implementing `FS.Pull.unfoldMaybe`
-- export
-- unfoldMaybeImpl :
--      SnocList o
--   -> Nat
--   -> (s -> Maybe (o,s))
--   -> s
--   -> (Chunk o, Maybe s)
-- unfoldMaybeImpl sx 0     f x = (cast sx, Just x)
-- unfoldMaybeImpl sx (S k) f x =
--   case f x of
--     Just (v,x2) => unfoldMaybeImpl (sx:<v) k f x2
--     Nothing     => (cast sx, Nothing)
--
-- ||| Utility for implementing `FS.Pull.iterate`
-- export
-- iterateImpl : SnocList o -> Nat -> (o -> o) -> o -> (Chunk o, Maybe o)
-- iterateImpl sx 0     f x = (cast sx, Just x)
-- iterateImpl sx (S k) f x = iterateImpl (sx :< x) k f (f x)
--
-- ||| Stack-safe implementation of `splitAt`
-- export
-- splitAt : Chunk a -> Nat -> (Chunk a, Chunk a)
-- splitAt (Bts bs) n =
--   case splitAt n bs of
--     Nothing      => (Bts bs, Bts empty)
--     (Just (x,y)) => (Bts x, Bts y)
-- splitAt (Lst vs) n = go [<] vs n
--   where
--     go : SnocList a -> List a -> Nat -> (Chunk a, Chunk a)
--     go sv (v::vs) (S k) = go (sv:<v) vs k
--     go sv vs      _     = (cast sv, cast vs)
--
-- -- ||| Used for implementing `FS.Pull.take`
-- -- export
-- -- take : SnocList o -> Nat -> List o -> (Nat, List o, List o)
-- -- take sx (S k) (x :: xs) = takeImpl (sx :< x) k xs
-- -- take sx k     xs        = (k, sx <>> [], xs)
-- --
-- -- takeImpl : SnocList o -> Nat -> List o -> (Nat, List o, List o)
-- -- takeImpl sx (S k) (x :: xs) = takeImpl (sx :< x) k xs
-- -- takeImpl sx k     xs        = (k, sx <>> [], xs)
-- --
-- -- ||| Used for implementing `FS.Pull.drop`
-- -- export
-- -- dropImpl : Nat -> List o -> (Nat, List o)
-- -- dropImpl (S k) (x :: xs) = dropImpl k xs
-- -- dropImpl k     xs        = (k, xs)
-- --
-- -- ||| Used for implementing `FS.Pull.takeWhile` and `FS.Pull.takeThrough`
-- -- export
-- -- takeWhileImpl : Bool -> SnocList o -> (o -> Bool) -> List o -> Maybe (List o,List o)
-- -- takeWhileImpl tf sx f []        = Nothing
-- -- takeWhileImpl tf sx f (x :: xs) =
-- --   if      f x then takeWhileImpl tf (sx :< x) f xs
-- --   else if tf  then Just (sx <>> [x], xs)
-- --   else             Just (sx <>> [], x::xs)
--
-- ||| Used for implementing `FS.Pull.takeWhileJust`
-- export
-- takeWhileJustImpl : SnocList o -> List (Maybe o) -> (Chunk o,List $ Maybe o)
-- takeWhileJustImpl sx []        = (cast sx, [])
-- takeWhileJustImpl sx (x :: xs) =
--   case x of
--     Nothing => (cast sx, Nothing :: xs)
--     Just v  => takeWhileJustImpl (sx :< v) xs
--
-- -- ||| Used for implementing `FS.Pull.dropWhile` and `FS.Pull.dropThrough`
-- -- export
-- -- dropWhileImpl : (o -> Bool) -> List o -> List o
-- -- dropWhileImpl f []        = []
-- -- dropWhileImpl f (x :: xs) = if f x then dropWhileImpl f xs else x::xs
-- --
-- ||| Used for implementing `FS.Pull.find`
-- export
-- find : (o -> Bool) -> Chunk o -> Maybe (o,Chunk o)
-- find f (Bts bs) =
--   case break f bs of
--     (_, BS (S k) v) => Just (head v, Bts (BS k $ tail v))
--     _               => Nothing
-- find f (Lst vs) = go vs
--   where
--     go : List o -> Maybe (o,Chunk o)
--     go []        = Nothing
--     go (x :: xs) = if f x then Just (x, Lst xs) else go xs
--
--
-- chunkedGo :
--      SnocList (Chunk a)
--   -> SnocList a
--   -> Nat
--   -> Nat
--   -> List a
--   -> List (Chunk a)
-- chunkedGo sxs sx _  _     []     = sxs <>> [cast sx]
-- chunkedGo sxs sx sz 0     (h::t) = chunkedGo (sxs :< (cast sx)) [<h] sz sz t
-- chunkedGo sxs sx sz (S m) (h::t) = chunkedGo sxs (sx:<h) sz m t
--
-- ||| Groups a list of values into chunks of size `n`.
-- |||
-- ||| Only the last list might be shorter.
-- export
-- chunked : (n : Nat) -> (0 p : IsSucc n) => List a -> List (Chunk a)
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
