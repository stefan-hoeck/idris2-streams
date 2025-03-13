||| Size-indexed chunks of data
module FS.Internal.IChunk

import Data.Array.Core
import Data.Array.Indexed
import Data.Buffer.Core
import Data.Buffer.Indexed
import Data.Nat.BSExtra
import Data.Vect

%default total

--------------------------------------------------------------------------------
-- IChunk
--------------------------------------------------------------------------------

||| A size-indexed chunk of values.
|||
||| Currently, the constructors are exported for reasons of convenience.
||| Please note, however, that the internal structure is an implementation
||| detail.
public export
data IChunk : Nat -> Type -> Type where
  Arr : (off : Nat) -> (0 lte : LTE (off+len) n) -> IArray n a -> IChunk len a
  Bts : (off : Nat) -> (0 lte : LTE (off+len) n) -> IBuffer n -> IChunk len Bits8

--------------------------------------------------------------------------------
-- Indexing
--------------------------------------------------------------------------------

||| Reads the value of an `IChunk` at the given position
export
at : IChunk n a -> Fin n -> a
at (Arr o lte arr) x =
  atNat arr (o + finToNat x) @{transitive (ltPlusRight $ finToNatLT x) lte}
at (Bts o lte buf) x =
  atNat buf (o + finToNat x) @{transitive (ltPlusRight $ finToNatLT x) lte}

||| Safely access a value in a chunk at position `n - m`.
export %inline
ix : IChunk n a -> (0 m : Nat) -> {auto x: Ix (S m) n} -> a
ix chnk _ = at chnk (ixToFin x)

||| Safely access the value in a chunk at the given position.
export %inline
atNat : IChunk n a -> (m : Nat) -> {auto 0 lt : LT m n} -> a
atNat bv x = at bv (natToFinLT x)

--------------------------------------------------------------------------------
-- Generating IChunks
--------------------------------------------------------------------------------

export %inline
fromArray : IArray n a -> IChunk n a
fromArray = Arr 0 reflexive

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

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export %inline
Cast (IArray n a) (IChunk n a) where
  cast = fromArray

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
