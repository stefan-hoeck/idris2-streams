||| Utilities for working with chunks of data.
module FS.Internal.Chunk

import Data.Nat

%default total

||| Utility for implementing `FS.Pull.unfold`
export
unfoldImpl :
     SnocList o
  -> Nat
  -> (s -> Either r (o,s))
  -> s
  -> (List o, Either r s)
unfoldImpl sx 0     f x = (sx <>> [], Right x)
unfoldImpl sx (S k) f x =
  case f x of
    Right (v,x2) => unfoldImpl (sx:<v) k f x2
    Left res     => (sx <>> [], Left res)

||| Utility for implementing `FS.Pull.unfoldMaybe`
export
unfoldMaybeImpl :
     SnocList o
  -> Nat
  -> (s -> Maybe (o,s))
  -> s
  -> (List o, Maybe s)
unfoldMaybeImpl sx 0     f x = (sx <>> [], Just x)
unfoldMaybeImpl sx (S k) f x =
  case f x of
    Just (v,x2) => unfoldMaybeImpl (sx:<v) k f x2
    Nothing     => (sx <>> [], Nothing)

||| Utility for implementing `FS.Pull.iterate`
export
iterateImpl : SnocList o -> Nat -> (o -> o) -> o -> (List o, Maybe o)
iterateImpl sx 0     f x = (sx <>> [], Just x)
iterateImpl sx (S k) f x = iterateImpl (sx :< x) k f (f x)

||| Stack-safe implementation of `splitAt`
export
splitAtImpl : SnocList a -> List a -> Nat -> (List a, List a)
splitAtImpl sv (v::vs) (S k) = splitAtImpl (sv:<v) vs k
splitAtImpl sv vs      _     = (sv <>> [], vs)

||| Used for implementing `FS.Pull.take`
export
takeImpl : SnocList o -> Nat -> List o -> (Nat, List o, List o)
takeImpl sx (S k) (x :: xs) = takeImpl (sx :< x) k xs
takeImpl sx k     xs        = (k, sx <>> [], xs)

||| Used for implementing `FS.Pull.drop`
export
dropImpl : Nat -> List o -> (Nat, List o)
dropImpl (S k) (x :: xs) = dropImpl k xs
dropImpl k     xs        = (k, xs)

||| Used for implementing `FS.Pull.takeWhile` and `FS.Pull.takeThrough`
export
takeWhileImpl : Bool -> SnocList o -> (o -> Bool) -> List o -> Maybe (List o,List o)
takeWhileImpl tf sx f []        = Nothing
takeWhileImpl tf sx f (x :: xs) =
  if      f x then takeWhileImpl tf (sx :< x) f xs
  else if tf  then Just (sx <>> [x], xs)
  else             Just (sx <>> [], x::xs)

||| Used for implementing `FS.Pull.dropWhile` and `FS.Pull.dropThrough`
export
dropWhileImpl : (o -> Bool) -> List o -> List o
dropWhileImpl f []        = []
dropWhileImpl f (x :: xs) = if f x then dropWhileImpl f xs else x::xs

||| Used for implementing `FS.Pull.find`
export
findImpl : (o -> Bool) -> List o -> Maybe (o,List o)
findImpl f []        = Nothing
findImpl f (x :: xs) = if f x then Just (x,xs) else findImpl f xs

chunkedGo :
     SnocList (List a)
  -> SnocList a
  -> Nat
  -> Nat
  -> List a
  -> List (List a)
chunkedGo sxs sx _  _     []     = sxs <>> [sx <>> []]
chunkedGo sxs sx sz 0     (h::t) = chunkedGo (sxs :< (sx <>> [])) [<h] sz sz t
chunkedGo sxs sx sz (S m) (h::t) = chunkedGo sxs (sx:<h) sz m t

||| Groups a list of values into chunks of size `n`.
|||
||| Only the last list might be shorter.
export
chunked : (n : Nat) -> (0 p : IsSucc n) => List a -> List (List a)
chunked _      []     = []
chunked (S sz) (h::t) = chunkedGo [<] [<h] sz sz t
