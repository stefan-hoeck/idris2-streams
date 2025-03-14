module Test.FS.Pull

import Control.Monad.Elin
import Data.List
import Data.Maybe
import Data.SnocList
import FS.Internal.Chunk
import FS.Pull

import public Test.FS.Util

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_output1 : Property
prop_output1 =
  property $ do
    v <- forAll bytes
    pullList (output1 v) === [v]

prop_output : Property
prop_output =
  property $ do
    vs <- forAll byteLists
    pullList (output vs) === vs

prop_outputChunks : Property
prop_outputChunks =
  property $ do
    vs <- forAll byteLists
    pullChunks (output vs) === nonEmpty [vs]

prop_foldable : Property
prop_foldable =
  property $ do
    sv <- forAll byteSnocLists
    pullList (foldable sv) === (sv <>> [])

prop_unfoldChunkLeft : Property
prop_unfoldChunkLeft =
  property $ do
    vs <- forAll byteLists
    let cs := pullChunks $ unfoldChunk () (const (vs, Left ()))
    case vs of
      [] => cs === []
      _  => cs === [vs]

prop_unfoldChunk : Property
prop_unfoldChunk =
  property $ do
    n <- forAll posNats
    pullChunks (unfoldChunk n next) === map (\x => replicate x x) [n..1]

  where
    next : Nat -> (List Nat, Either () Nat)
    next 0       = ([], Left ())
    next n@(S k) = (replicate n n, Right k)

prop_unfoldChunkMaybe : Property
prop_unfoldChunkMaybe =
  property $ do
    n <- forAll posNats
    pullChunks (unfoldChunkMaybe n next) === map (\x => replicate x x) [n..1]

  where
    next : Nat -> (List Nat, Maybe Nat)
    next 0       = ([], Nothing)
    next n@(S k) = (replicate n n, Just k)

prop_unfold : Property
prop_unfold =
  property $ do
    n <- forAll posNats
    pullList (unfold n next) === map (\x => x * x) [n..1]
  where
    next : Nat -> Either () (Nat,Nat)
    next 0       = Left ()
    next n@(S k) = Right (n*n,k)

prop_unfoldAsChunks : Property
prop_unfoldAsChunks =
  property $ do
    [cs,n] <- forAll $ hlist [chunkSizes, posNats]
    pullChunks (unfold @{cs} n next) === chunkedCS cs (map (\x => x * x) [n..1])
  where
    next : Nat -> Either () (Nat,Nat)
    next 0       = Left ()
    next n@(S k) = Right (n*n,k)

prop_unfoldMaybe : Property
prop_unfoldMaybe =
  property $ do
    n <- forAll posNats
    pullList (unfoldMaybe n next) === map (\x => x * x) [n..1]

  where
    next : Nat -> Maybe (Nat,Nat)
    next 0       = Nothing
    next n@(S k) = Just (n*n,k)

prop_unfoldMaybeAsChunks : Property
prop_unfoldMaybeAsChunks =
  property $ do
    [cs,n] <- forAll $ hlist [chunkSizes, posNats]
    pullChunks (unfoldMaybe @{cs} n next) === chunkedCS cs (map (\x => x * x) [n..1])

  where
    next : Nat -> Maybe (Nat,Nat)
    next 0       = Nothing
    next n@(S k) = Just (n*n,k)

prop_fill : Property
prop_fill =
  property $ do
    [n,v] <- forAll $ hlist [smallNats, bytes]
    pullList (ignore $ take n $ fill v) === replicate n v

prop_fillChunks : Property
prop_fillChunks =
  property $ do
    [cs, n,v] <- forAll $ hlist [chunkSizes, smallNats, bytes]
    pullChunks (ignore $ take n $ fill @{cs} v) === chunkedCS cs (replicate n v)

prop_iterate : Property
prop_iterate =
  property $ do
    n <- forAll posNats
    pullList (ignore $ take n $ iterate 0 S) === [0..pred n]

prop_iterateChunks : Property
prop_iterateChunks =
  property $ do
    [cs,n] <- forAll $ hlist [chunkSizes, posNats]
    pullChunks (ignore $ take n $ iterate @{cs} 0 S) === chunkedCS cs [0..pred n]

prop_replicate : Property
prop_replicate =
  property $ do
    [n,v] <- forAll $ hlist [smallNats, bytes]
    pullList (replicate n v) === replicate n v

prop_replicateChunks : Property
prop_replicateChunks =
  property $ do
    [cs,n,v] <- forAll $ hlist [chunkSizes, smallNats, bytes]
    pullChunks (replicate @{cs} n v) === chunkedCS cs (replicate n v)

prop_fromChunks : Property
prop_fromChunks =
  property $ do
    vss <- forAll byteChunks
    pullChunks (fromChunks vss) === nonEmpty vss

prop_cons : Property
prop_cons =
  property $ do
    [vs,vss] <- forAll $ hlist [byteLists, byteChunks]
    pullChunks (cons vs $ fromChunks vss) === nonEmpty (vs::vss)

prop_uncons : Property
prop_uncons =
  property $ do
    vss <- forAll byteChunks
    pullChunks (uncons (fromChunks vss) >>= headOut) === firstNotNull vss

prop_unconsrem : Property
prop_unconsrem =
  property $ do
    vss <- forAll byteChunks
    pullChunks (uncons (fromChunks vss) >>= tailOut) === drop 1 (nonEmpty vss)

prop_uncons1 : Property
prop_uncons1 =
  property $ do
    vss <- forAll byteChunks
    pullChunks (uncons1 (fromChunks vss) >>= headOut1) === firstl vss

prop_unconsLimit : Property
prop_unconsLimit =
  property $ do
    [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
    let res := pullChunks (unconsLimit n (fromChunks vss) >>= headOut)
    case nonEmpty vss of
      h::_ => res === [take n h]
      _    => res === []

prop_unconsMinFalse : Property
prop_unconsMinFalse =
  property $ do
    [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
    let res := pullList (unconsMin n False (fromChunks vss) >>= headOut)
        all := concat vss
    case length all >= n of
      True  => assert (isPrefixOf res all && length res >= n)
      False => res === []

prop_unconsMinTrue : Property
prop_unconsMinTrue =
  property $ do
    [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
    let res := pullList (unconsMin n True (fromChunks vss) >>= headOut)
        all := concat vss
    case length all >= n of
      True  => assert (isPrefixOf res all && length res >= n)
      False => res === all

prop_unconsNFalse : Property
prop_unconsNFalse =
  property $ do
    [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
    let res := pullList (unconsN n False (fromChunks vss) >>= headOut)
        all := concat vss
    case length all >= n of
      True  => assert (isPrefixOf res all && length res == n)
      False => res === []

prop_unconsNTrue : Property
prop_unconsNTrue =
  property $ do
    [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
    let res := pullList (unconsN n True (fromChunks vss) >>= headOut)
        all := concat vss
    case length all >= n of
      True  => assert (isPrefixOf res all && length res == n)
      False => res === all

prop_take : Property
prop_take =
  property $ do
    [n, vss] <- forAll $ hlist [smallNats, byteChunks]
    pullList (ignore $ take n (fromChunks vss)) === take n (join vss)

prop_takerem : Property
prop_takerem =
  property $ do
    [n, vss] <- forAll $ hlist [smallNats, byteChunks]
    pullList (take n (fromChunks vss) >>= orEmpty) === join vss

prop_takeRight : Property
prop_takeRight =
  property $ do
    [n, vss] <- forAll $ hlist [smallNats, byteChunks]
    pullList (takeRight (S n) (fromChunks vss) >>= output) ===
      reverse (take (S n) . reverse $ join vss)

prop_last : Property
prop_last =
  property $ do
    vss <- forAll byteChunks
    pullList (last (fromChunks vss) >>= traverse_ output1) === lastl (join vss)

prop_peek : Property
prop_peek =
  property $ do
    vss <- forAll byteChunks
    pullChunks (peek (fromChunks vss) >>= headOut) === firstNotNull vss

prop_peekrem : Property
prop_peekrem =
  property $ do
    vss <- forAll byteChunks
    pullChunks (peek (fromChunks vss) >>= tailOut) === nonEmpty vss

prop_peek1 : Property
prop_peek1 =
  property $ do
    vss <- forAll byteChunks
    pullChunks (peek1 (fromChunks vss) >>= headOut1) === firstl vss

prop_peek1rem : Property
prop_peek1rem =
  property $ do
    vss <- forAll byteChunks
    pullChunks (peek1 (fromChunks vss) >>= tailOut) === nonEmpty vss

prop_takeWhileRem : Property
prop_takeWhileRem =
  property $ do
    vss <- forAll byteChunks
    pullList (takeWhile (< 10) (fromChunks vss) >>= orEmpty) ===
      join vss

prop_takeThroughRem : Property
prop_takeThroughRem =
  property $ do
    vss <- forAll byteChunks
    pullList (takeThrough (< 10) (fromChunks vss) >>= orEmpty) ===
      join vss

prop_find : Property
prop_find =
  property $ do
    vss <- forAll byteChunks
    pullList (find (> 10) (fromChunks vss) >>= emitBoth1) ===
      dropWhile (<= 10) (join vss)

prop_foldChunks : Property
prop_foldChunks =
  property $ do
    vss <- forAll byteChunks
    pullList (foldChunks (the Bits8 0) (\n => (n+) . sum) (fromChunks vss) >>= output1) ===
      [sum $ join vss]

prop_fold : Property
prop_fold =
  property $ do
    vss <- forAll byteChunks
    pullList (fold 0 (+) (fromChunks vss) >>= output1) === [sum $ join vss]

--------------------------------------------------------------------------------
-- Group
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup "FS.Pull"
    [ ("prop_output1", prop_output1)
    , ("prop_output", prop_output)
    , ("prop_outputChunks", prop_outputChunks)
    , ("prop_foldable", prop_foldable)
    , ("prop_unfoldChunkLeft", prop_unfoldChunkLeft)
    , ("prop_unfoldChunk", prop_unfoldChunk)
    , ("prop_unfoldChunkMaybe", prop_unfoldChunkMaybe)
    , ("prop_unfold", prop_unfold)
    , ("prop_unfoldAsChunks", prop_unfoldAsChunks)
    , ("prop_unfoldMaybe", prop_unfoldMaybe)
    , ("prop_unfoldMaybeAsChunks", prop_unfoldMaybeAsChunks)
    , ("prop_fill", prop_fill)
    , ("prop_fillChunks", prop_fillChunks)
    , ("prop_iterate", prop_iterate)
    , ("prop_iterateChunks", prop_iterateChunks)
    , ("prop_replicate", prop_replicate)
    , ("prop_replicateChunks", prop_replicateChunks)
    , ("prop_fromChunks", prop_fromChunks)
    , ("prop_cons", prop_cons)
    , ("prop_uncons", prop_uncons)
    , ("prop_unconsrem", prop_unconsrem)
    , ("prop_uncons1", prop_uncons1)
    , ("prop_unconsLimit", prop_unconsLimit)
    , ("prop_unconsMinFalse", prop_unconsMinFalse)
    , ("prop_unconsMinTrue", prop_unconsMinTrue)
    , ("prop_unconsNFalse", prop_unconsNFalse)
    , ("prop_unconsNTrue", prop_unconsNTrue)
    , ("prop_take", prop_take)
    , ("prop_takerem", prop_takerem)
    , ("prop_takeRight", prop_takeRight)
    , ("prop_takeWhileRem", prop_takeWhileRem)
    , ("prop_takeThroughRem", prop_takeThroughRem)
    , ("prop_last", prop_last)
    , ("prop_peek", prop_peek)
    , ("prop_peekrem", prop_peekrem)
    , ("prop_peek1", prop_peek1)
    , ("prop_peek1rem", prop_peek1rem)
    , ("prop_find", prop_find)
    , ("prop_foldChunks", prop_foldChunks)
    , ("prop_fold", prop_fold)
    ]
