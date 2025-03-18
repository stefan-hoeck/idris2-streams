||| Utilities for working with chunks of data.
module FS.Chunk

import Control.Monad.Identity
import Data.List1
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
-- Unfold
--------------------------------------------------------------------------------

%inline
fromSnoc : o -> SnocList o -> List1 o
fromSnoc h t = h ::: (t <>> [])

public export
data UnfoldRes : (r,s,o : Type) -> Type where
  Chunk : (vals : o) -> (st : s) -> UnfoldRes r s o
  Done  : (res : r) ->  UnfoldRes r s o
  Last  : (res : r) ->  (vals : o) -> UnfoldRes r s o

public export
interface Unfold (0 c,o : Type) | c where
  unfoldImpl : ChunkSize => (s ->  Either r (o,s)) -> s -> UnfoldRes r s c

unfoldList :
     o
  -> SnocList o
  -> Nat
  -> (s -> Either r (o,s))
  -> s
  -> UnfoldRes r s (List1 o)
unfoldList hd sx 0     f x = Chunk (fromSnoc hd sx) x
unfoldList hd sx (S k) f x =
  case f x of
    Right (v,x2) => unfoldList hd (sx:<v) k f x2
    Left res     => Last res (fromSnoc hd sx)

export
Unfold (List1 a) a where
  unfoldImpl @{CS (S n)} f x =
    case f x of
      Left res     => Done res
      Right (v,x2) => unfoldList v [<] n f x2

export
Unfold (Identity a) a where
  unfoldImpl f x =
    case f x of
      Left res     => Done res
      Right (v,x2) => Chunk (Id v) x2

--------------------------------------------------------------------------------
-- Uncons
--------------------------------------------------------------------------------

public export
interface Uncons (0 c, o : Type) | c where
  unconsImpl : c -> (o, Maybe c)

export %inline
Uncons (Identity o) o where
  unconsImpl (Id v) = (v, Nothing)

export %inline
Uncons (List1 o) o where
  unconsImpl (v:::[])   = (v, Nothing)
  unconsImpl (v:::h::t) = (v, Just $ h:::t)

--------------------------------------------------------------------------------
-- Split
--------------------------------------------------------------------------------

public export
data SplitRes : Type -> Type where
  Middle : (pre, post : c) -> SplitRes c
  Naught : SplitRes c
  All    : c -> Nat -> SplitRes c

public export
interface Split (0 c : Type) where
  splitAt : Nat -> c -> SplitRes c

export %inline
Split (Identity a) where
  splitAt 0     _ = Naught
  splitAt (S k) i = All i k

splitAtList : o -> SnocList o -> Nat -> List o -> SplitRes (List1 o)
splitAtList x sx (S k) (h::t) = splitAtList x (sx :< h) k t
splitAtList x sx n     []     = All (fromSnoc x sx) n
splitAtList x sx 0     (h::t) = Middle (fromSnoc x sx) (h:::t)

export %inline
Split (List1 a) where
  splitAt 0     _       = Naught
  splitAt (S k) (h:::t) = splitAtList h [<] k t

--------------------------------------------------------------------------------
-- Break
--------------------------------------------------------------------------------

public export
data BreakRes : Type -> Type where
  Broke : (pre, post : c) -> BreakRes c
  First : BreakRes c
  None  : BreakRes c

public export
interface Break (0 c,o : Type) | c where
  breakImpl : (o -> Bool) -> c -> BreakRes c

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
