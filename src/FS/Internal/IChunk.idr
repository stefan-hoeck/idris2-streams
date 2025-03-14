||| Size-indexed chunks of data
module FS.Internal.IChunk

import Data.Array.Core
import Data.Array.Indexed
import Data.Buffer.Core
import Data.Buffer.Indexed
import Data.ByteVect
import Data.Nat.BSExtra
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- IChunk
--------------------------------------------------------------------------------

public export
data Inner : Nat -> Type -> Type where
  Arr : IArray n a -> Inner n a
  Bts : IBuffer n -> Inner n Bits8

||| A size-indexed chunk of values.
|||
||| Currently, the constructors are exported for reasons of convenience.
||| Please note, however, that the internal structure is an implementation
||| detail.
public export
record IChunk n a where
  constructor C
  {0 len  : Nat}
  offset  : Nat
  0 lte   : LTE (offset+n) len
  values  : Inner len a

--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------

||| Reads the value of an `IChunk` at the given position
export
at : IChunk n a -> Fin n -> a
at (C o p arr) x =
 let 0 prf := transitive (ltPlusRight $ finToNatLT x) p
  in case arr of
       Arr vs => atNat vs (o + finToNat x) @{prf}
       Bts vs => atNat vs (o + finToNat x) @{prf}

||| Safely access a value in a chunk at position `n - m`.
export %inline
ix : IChunk n a -> (0 m : Nat) -> {auto x: Ix (S m) n} -> a
ix chnk _ = at chnk (ixToFin x)

||| Safely access the value in a chunk at the given position.
export %inline
atNat : IChunk n a -> (m : Nat) -> {auto 0 lt : LT m n} -> a
atNat bv x = at bv (natToFinLT x)

export %inline
head : IChunk (S n) a -> a
head c = at c 0

--------------------------------------------------------------------------------
-- Generating IChunks
--------------------------------------------------------------------------------

export %inline
fromArray : IArray n a -> IChunk n a
fromArray arr = C 0 reflexive (Arr arr)

export %inline
fill : (n : Nat) -> a -> IChunk n a
fill n = fromArray . fill n

export %inline
generate : (n : Nat) -> (Fin n -> a) -> IChunk n a
generate n = fromArray . generate n

export %inline
iterate : (n : Nat) -> (a -> a) -> a -> IChunk n a
iterate n f = fromArray . iterate n f

||| Copy the values in a list to an array of the same length.
export %inline
chunkL : (ls : List a) -> IChunk (length ls) a
chunkL xs = fromArray $ arrayL xs

||| Copy the values in a vector to an array of the same length.
export %inline
chunk : {n : _} -> Vect n a -> IChunk n a
chunk xs = fromArray $ array xs

||| Wrap a byte vector in an indexed chunk.
export %inline
fromByteVect : ByteVect n -> IChunk n Bits8
fromByteVect (BV b o p) = C o p (Bts b)

||| Wrap a byte vector in an indexed chunk.
export %inline
fromBuffer : IBuffer n -> IChunk n Bits8
fromBuffer buf = C 0 reflexive (Bts buf)

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export %inline
Cast (IArray n a) (IChunk n a) where
  cast = fromArray

export %inline
{n : _} -> Cast (Vect n a) (IChunk n a) where
  cast = chunk

export %inline
Cast (ByteVect n) (IChunk n Bits8) where
  cast = fromByteVect

export %inline
Cast (IBuffer n) (IChunk n Bits8) where
  cast = fromBuffer

export %inline
{n : _} -> Functor (IChunk n) where
  map f chnk = generate n (f . at chnk)

||| Lexicographic comparison of Arrays of distinct length
export
hcomp : {m,n : Nat} -> Ord a => IChunk m a -> IChunk n a -> Ordering
hcomp a1 a2 = go m n

  where
    go : (k,l : Nat) -> {auto _ : Ix k m} -> {auto _ : Ix l n} -> Ordering
    go 0     0     = EQ
    go 0     (S _) = LT
    go (S _) 0     = GT
    go (S k) (S j) = case compare (ix a1 k) (ix a2 j) of
      EQ => go k j
      r  => r

||| Heterogeneous equality for Arrays
export
heq : {m,n : Nat} -> Eq a => IChunk m a -> IChunk n a -> Bool
heq a1 a2 = go m n

  where
    go : (k,l : Nat) -> {auto _ : Ix k m} -> {auto _ : Ix l n} -> Bool
    go 0     0     = True
    go (S k) (S j) = if ix a1 k == ix a2 j then go k j else False
    go _     _     = False

export
{n : Nat} -> Eq a => Eq (IChunk n a) where
  a1 == a2 = go n

    where
      go : (k : Nat) -> {auto 0 _ : LTE k n} -> Bool
      go 0     = True
      go (S k) = if atNat a1 k == atNat a2 k then go k else False

export
{n : Nat} -> Ord a => Ord (IChunk n a) where
  compare a1 a2 = go n

    where
      go : (k : Nat) -> {auto _ : Ix k n} -> Ordering
      go 0     = EQ
      go (S k) = case compare (ix a1 k) (ix a2 k) of
        EQ => go k
        c  => c

ontoList : List a -> (m : Nat) -> (0 lte : LTE m n) => IChunk n a -> List a
ontoList xs 0     arr = xs
ontoList xs (S k) arr = ontoList (atNat arr k :: xs) k arr

foldrI : (m : Nat) -> (0 _ : LTE m n) => (e -> a -> a) -> a -> IChunk n e -> a
foldrI 0     _ x arr = x
foldrI (S k) f x arr = foldrI k f (f (atNat arr k) x) arr

foldlI : (m : Nat) -> (x : Ix m n) => (a -> e -> a) -> a -> IChunk n e -> a
foldlI 0     _ v arr = v
foldlI (S k) f v arr = foldlI k f (f v (ix arr k)) arr

export
{n : _} -> Foldable (IChunk n) where
  foldr = foldrI n
  foldl = foldlI n
  foldMap f = foldr (\v => (f v <+>)) neutral
  toList = ontoList [] n
  null _ = n == Z

--------------------------------------------------------------------------------
-- Subchunks
--------------------------------------------------------------------------------

||| Return an `IChunk` with the first `n` values of
||| the input string. O(1)
export
take : (0 k : Nat) -> (0 lt : LTE k n) => IChunk n a -> IChunk k a
take k (C o p arr) = C o (transitive (ltePlusRight o lt) p) arr

||| Remove the first `n` values from an `IChunk`. O(1)
export
drop : (k : Nat) -> (0 lt : LTE k n) => IChunk n a -> IChunk (n `minus` k) a
drop k (C o p arr) =
  -- p        : o + n             <= bufLen
  -- lt       : k                 <= n
  -- required : (o + k) + (n - k) <= bufLen
  let 0 q := cong (o +) (plusMinus k n lt)
      0 r := plusAssociative o k (n `minus` k)
   in C (o + k) (rewrite (trans (sym r) q) in p) arr
