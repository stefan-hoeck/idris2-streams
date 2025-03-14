||| Utilities for working with chunks of data.
module Data.Chunk

import Data.Array.Core as AC
import Data.Array.Mutable
import Data.ByteString

import public Data.Chunk.Indexed
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
-- Making Chunks
--------------------------------------------------------------------------------

export %inline
empty : Chunk a
empty = wrap iempty

export %inline
fill : (n : Nat) -> a -> Chunk a
fill n = wrap . fromIArray . fill n

export %inline
generate : (n : Nat) -> (Fin n -> a) -> Chunk a
generate n = wrap . fromIArray . generate n

export %inline
iterate : (n : Nat) -> (a -> a) -> a -> Chunk a
iterate n f = wrap . fromIArray . iterate n f

||| Copy the values in a list to an array of the same length.
export %inline
chunkL : (ls : List a) -> Chunk a
chunkL xs = wrap $ fromIArray $ arrayL xs

||| Wrap an array in a chunk.
export %inline
values : Array a -> Chunk a
values (A sz bv) = C sz (fromIArray bv)

||| Wrap a byte string in a chunk.
export %inline
bytes : ByteString -> Chunk Bits8
bytes (BS sz bv) = C sz (fromByteVect bv)

export %inline
singleton : a -> Chunk a
singleton v = fill 1 v

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export %inline
Semigroup (Chunk a) where
  C _ x <+> C _ y = C _ (append x y)

export %inline
Monoid (Chunk a) where
  neutral = empty

export
uncons : Chunk a -> Maybe (a, Chunk a)
uncons (C (S k) arr) = Just (head arr, wrap $ tail arr)
uncons _             = Nothing

--------------------------------------------------------------------------------
-- Utilities
--------------------------------------------------------------------------------

generateMaybe : (n : Nat) -> (Fin n -> Maybe a) -> Chunk a
generateMaybe n f = unsafeAlloc n (go n n)
  where
    go : (k,m : Nat) -> (x : Ix k n) => (y : Ix m n) => WithMArray n a (Chunk a)
    go (S k) (S m) r t =
      case f (ixToFin x) of
        Nothing => go k (S m) r t
        Just v  => let _ # t := setIx r m v t in go k m r t
    go _ _ r t =
      let arr # t := AC.unsafeFreezeLTE @{ixLTE y} r (ixToNat y) t
       in wrap (fromIArray arr) # t

export
generateImpl :
     SnocList o
  -> (st -> Either r (o,st))
  -> Nat
  -> st
  -> (Chunk o, Either r st)
generateImpl so fun 0     cur = (cast so, Right cur)
generateImpl so fun (S k) cur =
  case fun cur of
    Right (v,next) => generateImpl (so :< v) fun k next
    Left res       => (cast so, Left res)

export
filter : (a -> Bool) -> Chunk a -> Chunk a
filter pred (C n ic@(IC o p rep)) =
  case rep of
    Bts buf => bytes (filter pred $ BV buf o p)
    Arr arr =>
      generateMaybe n $
        \x => let v := at ic x in if pred v then Just v else Nothing

export %inline
mapMaybe : (a -> Maybe b) -> Chunk a -> Chunk b
mapMaybe fun (C n ic) = generateMaybe n $ \x => fun (at ic x)

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
||| Utility for implementing `FS.Pull.unfoldMaybe`
export
unfoldMaybeImpl :
     SnocList o
  -> Nat
  -> (s -> Maybe (o,s))
  -> s
  -> (Chunk o, Maybe s)
unfoldMaybeImpl sx 0     f x = (cast sx, Just x)
unfoldMaybeImpl sx (S k) f x =
  case f x of
    Just (v,x2) => unfoldMaybeImpl (sx:<v) k f x2
    Nothing     => (cast sx, Nothing)

||| Utility for implementing `FS.Pull.iterate`
export
iterateImpl : SnocList o -> Nat -> (o -> o) -> o -> (Chunk o, Maybe o)
iterateImpl sx 0     f x = (cast sx, Just x)
iterateImpl sx (S k) f x = iterateImpl (sx :< x) k f (f x)

export
splitAt : Chunk a -> Nat -> (Chunk a, Chunk a)
splitAt ch@(C sz arr) n with (n < sz) proof eq
  _ | True  =
    let 0 lte := ltOpReflectsLT n sz eq
     in (C _ $ take n arr, C _ $ drop n arr)
  _ | False = (ch, empty)

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
||| Used for implementing `FS.Pull.takeWhileJust`
export
takeWhileJustImpl : Chunk (Maybe o) -> (Chunk o,Chunk $ Maybe o)
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

||| Used for implementing `FS.Pull.find`
export
find : (o -> Bool) -> Chunk o -> Maybe (o,Chunk o)
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
