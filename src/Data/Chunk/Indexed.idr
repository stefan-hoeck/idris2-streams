||| Size-indexed chunks of data
module Data.Chunk.Indexed

import Data.Array.Core as AC
import Data.Array.Indexed
import Data.Array.Mutable as MA

import Data.Buffer.Core as BC
import Data.Buffer.Indexed
import Data.Buffer.Mutable as MB

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
  constructor IC
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
at (IC o p arr) x =
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
iempty : IChunk 0 a
iempty = IC 0 LTEZero (Arr empty)

export %inline
fromIArray : IArray n a -> IChunk n a
fromIArray arr = IC 0 reflexive (Arr arr)

export %inline
igenerate : (n : Nat) -> (Fin n -> a) -> IChunk n a
igenerate n = fromIArray . generate n

||| Copy the values in a list to an array of the same length.
export %inline
ichunkL : (ls : List a) -> IChunk (length ls) a
ichunkL xs = fromIArray $ arrayL xs

||| Copy the values in a vector to an array of the same length.
export %inline
ichunk : {n : _} -> Vect n a -> IChunk n a
ichunk xs = fromIArray $ array xs

||| Wrap a byte vector in an indexed chunk.
export %inline
fromByteVect : ByteVect n -> IChunk n Bits8
fromByteVect (BV b o p) = IC o p (Bts b)

||| Wrap a byte vector in an indexed chunk.
export %inline
fromIBuffer : IBuffer n -> IChunk n Bits8
fromIBuffer buf = IC 0 reflexive (Bts buf)

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export %inline
Cast (IArray n a) (IChunk n a) where
  cast = fromIArray

export %inline
{n : _} -> Cast (Vect n a) (IChunk n a) where
  cast = ichunk

export %inline
Cast (ByteVect n) (IChunk n Bits8) where
  cast = fromByteVect

export %inline
Cast (IBuffer n) (IChunk n Bits8) where
  cast = fromIBuffer

export %inline
{n : _} -> Functor (IChunk n) where
  map f chnk = igenerate n (f . at chnk)

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

export
{n : _} -> Show a => Show (IChunk n a) where
  showPrec p ic = showCon p "ichunkL" (showArg $ toList ic)

--------------------------------------------------------------------------------
-- Non-indexed Chunks
--------------------------------------------------------------------------------

public export
record Chunk a where
  constructor C
  size   : Nat
  values : IChunk size a

export %inline
wrap : {n : _} -> IChunk n a -> Chunk a
wrap = C n

export
Eq a => Eq (Chunk a) where
  C l1 c1 == C l2 c2 = heq c1 c2

export
Ord a => Ord (Chunk a) where
  compare (C l1 c1) (C l2 c2) = hcomp c1 c2

export
Show a => Show (Chunk a) where
  showPrec p (C sz vs) = showCon p "C" (showArg sz ++ showArg vs)

export
Functor Chunk where
  map f (C n vs) = C n $ map f vs

export
Foldable Chunk where
  foldl f i (C _ vs) = foldl f i vs
  foldr f i (C _ vs) = foldr f i vs
  foldMap f (C _ vs) = foldMap f vs
  toList (C _ vs) = toList vs
  null (C 0 _) = True
  null _       = False

export %inline
Cast (List a) (Chunk a) where
  cast vs = C _ $ ichunkL vs

export %inline
Cast (SnocList a) (Chunk a) where
  cast = cast . (<>> [])

--------------------------------------------------------------------------------
-- Generating Chunks
--------------------------------------------------------------------------------

%inline
freezeChunk : Ix m n -> MArray s n a -> (Chunk a -> b) -> F1 s b
freezeChunk ix x fun t =
  let arr # t := AC.unsafeFreeze x t
   in fun (C (ixToNat ix) (IC 0 (ixLTE _) $ Arr arr)) # t

--------------------------------------------------------------------------------
-- Subchunks
--------------------------------------------------------------------------------

||| Return an `IChunk` with the first `n` values of
||| the input string. O(1)
export %inline
take : (0 k : Nat) -> (0 lt : LTE k n) => IChunk n a -> IChunk k a
take k (IC o p arr) = IC o (transitive (ltePlusRight o lt) p) arr

export %inline
takeIx : (x : Ix m n) -> IChunk n a -> IChunk (ixToNat x) a
takeIx x = take (ixToNat x) @{ixLTE x}

||| Remove the first `n` values from an `IChunk`. O(1)
export %inline
drop : (k : Nat) -> (0 lt : LTE k n) => IChunk n a -> IChunk (n `minus` k) a
drop k (IC o p arr) =
  -- p        : o + n             <= bufLen
  -- lt       : k                 <= n
  -- required : (o + k) + (n - k) <= bufLen
  let 0 q := cong (o +) (plusMinus k n lt)
      0 r := plusAssociative o k (n `minus` k)
   in IC (o + k) (rewrite (trans (sym r) q) in p) arr

export %inline
dropIx : (x : Ix m n) -> IChunk n a -> IChunk (n `minus` ixToNat x) a
dropIx x = drop (ixToNat x) @{ixLTE x}

||| Drop the first value from a non-empty chunk. O(1)
export %inline
tail : IChunk (S n) a -> IChunk n a
tail (IC o p arr) = IC (S o) (ltePlusSuccRight p) arr

--------------------------------------------------------------------------------
-- Concatenating Chunks
--------------------------------------------------------------------------------

export %inline
copyBytes :
     Inner m Bits8
  -> (srcOffset,dstOffset : Nat)
  -> (len : Nat)
  -> {auto 0 p1 : LTE (srcOffset + len) m}
  -> {auto 0 p2 : LTE (dstOffset + len) n}
  -> (r         : MBuffer s n)
  -> F1' s
copyBytes (Arr x)= icopyToBuf x
copyBytes (Bts x)= BC.icopy x

||| Concatenate two `Chunk`s. O(n + m).
export
append : {m,n : _} -> IChunk m a -> IChunk n a  -> IChunk (m + n) a
append {m = 0} _  c2 = c2
append {n = 0} c1 _  = rewrite plusZeroRightNeutral m in c1
append (IC o1 lte1 (Bts src1)) (IC o2 lte2 src2) =
  run1 $ \t =>
   let arr # t := mbuffer1 (m+n) t
       _   # t := BC.icopy {n = m+n} src1 o1 0 m @{lte1} @{lteAddRight _} arr t
       _   # t := copyBytes src2 o2 m n @{lte2} @{reflexive} arr t
       frz # t := BC.unsafeFreeze arr t
    in IC 0 reflexive (Bts frz) # t
append (IC o1 lte1 (Arr src1)) (IC o2 lte2 s2)   =
  case s2 of
    Bts src2 => run1 $ \t =>
     let arr # t := mbuffer1 (m+n) t
         _   # t := AC.icopyToBuf {n = m+n} src1 o1 0 m @{lte1} @{lteAddRight _} arr t
         _   # t := BC.icopy src2 o2 m n @{lte2} @{reflexive} arr t
         frz # t := BC.unsafeFreeze arr t
      in IC 0 reflexive (Bts frz) # t
    Arr src2 => run1 $ \t =>
     let arr # t := unsafeMArray1 (m+n) t
         _   # t := AC.icopy {n = m+n} src1 o1 0 m @{lte1} @{lteAddRight _} arr t
         _   # t := AC.icopy src2 o2 m n @{lte2} @{reflexive} arr t
         frz # t := AC.unsafeFreeze arr t
      in IC 0 reflexive (Arr frz) # t
