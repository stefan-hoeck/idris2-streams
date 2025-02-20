module Test.FS.Stream

import Control.Monad.Elin
import Data.List
import FS.Pull
import FS.Stream
import Test.FS.Util

||| Runs a `Stream` to completion, collecting all output in a list.
export
runEStream : (forall s . Stream (Elin s) es o) -> Result es (List o)
runEStream p = runElin (toList p)

||| Like `runEStream`, but without the possibility of failure.
export
runStream : (forall s . Stream (Elin s) [] o) -> List o
runStream p = either absurd id $ runEStream p

||| Runs a `Stream` to completion, collecting all chunks of output in a list.
||| This allows us to observe the chunk structure of a `Stream`.
export
sechunks : (forall s . Stream (Elin s) es o) -> Result es (List $ List o)
sechunks p = runElin (toChunks p)

||| Like `echunks`, but without the possibility of failure.
export
schunks : (forall s . Stream (Elin s) [] o) -> List (List o)
schunks p = either absurd id $ sechunks p

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_emit : Property
prop_emit =
  property $ do
    v <- forAll bytes
    runStream (emit v) === [v]

prop_emits : Property
prop_emits =
  property $ do
    vs <- forAll byteLists
    runStream (emits vs) === vs

prop_emitsChunks : Property
prop_emitsChunks =
  property $ do
    vs <- forAll byteLists
    schunks (emits vs) === nonEmpty [vs]

prop_unfoldChunk : Property
prop_unfoldChunk =
  property $ do
    n <- forAll posNats
    schunks (unfoldChunk n next) === map (\x => replicate x x) [n..1]

  where
    next : Nat -> (List Nat, Maybe Nat)
    next 0       = ([], Nothing)
    next n@(S k) = (replicate n n, Just k)

prop_unfold : Property
prop_unfold =
  property $ do
    n <- forAll posNats
    runStream (unfold n next) === map (\x => x * x) [n..1]
  where
    next : Nat -> Maybe (Nat,Nat)
    next 0       = Nothing
    next n@(S k) = Just (n*n,k)

prop_unfoldAsChunks : Property
prop_unfoldAsChunks =
  property $ do
    [cs,n] <- forAll $ hlist [chunkSizes, posNats]
    schunks (unfold @{cs} n next) === chunkedCS cs (map (\x => x * x) [n..1])
  where
    next : Nat -> Maybe (Nat,Nat)
    next 0       = Nothing
    next n@(S k) = Just (n*n,k)

prop_constant : Property
prop_constant =
  property $ do
    [n,v] <- forAll $ hlist [smallNats, bytes]
    runStream (take n $ constant v) === replicate n v

prop_constantChunks : Property
prop_constantChunks =
  property $ do
    [cs, n,v] <- forAll $ hlist [chunkSizes, smallNats, bytes]
    schunks (take n $ constant @{cs} v) === chunkedCS cs (replicate n v)

prop_iterate : Property
prop_iterate =
  property $ do
    n <- forAll posNats
    runStream (take n $ iterate 0 S) === [0..pred n]

prop_iterateChunks : Property
prop_iterateChunks =
  property $ do
    [cs,n] <- forAll $ hlist [chunkSizes, posNats]
    schunks (take n $ iterate @{cs} 0 S) === chunkedCS cs [0..pred n]

prop_fromChunks : Property
prop_fromChunks =
  property $ do
    vss <- forAll byteChunks
    schunks (fromChunks vss) === filter (not . null) vss

prop_cons : Property
prop_cons =
  property $ do
    [vs,vss] <- forAll $ hlist [byteLists, byteChunks]
    schunks (cons vs $ fromChunks vss) === filter (not . null) (vs::vss)

prop_cons1 : Property
prop_cons1 =
  property $ do
    [v,vss] <- forAll $ hlist [bytes, byteChunks]
    schunks (cons1 v $ fromChunks vss) === filter (not . null) ([v]::vss)

prop_append : Property
prop_append =
  property $ do
    [vss,wss] <- forAll $ hlist [byteChunks, byteChunks]
    schunks (fromChunks vss ++ fromChunks wss) === filter (not . null) (vss++wss)

prop_take : Property
prop_take =
  property $ do
    [n, vss] <- forAll $ hlist [smallNats, byteChunks]
    runStream (take n (fromChunks vss)) === take n (join vss)

prop_replicate : Property
prop_replicate =
  property $ do
    [n,v] <- forAll $ hlist [smallNats, bytes]
    runStream (replicate n v) === replicate n v

prop_replicateChunks : Property
prop_replicateChunks =
  property $ do
    [cs,n,v] <- forAll $ hlist [chunkSizes, smallNats, bytes]
    schunks (replicate @{cs} n v) === chunkedCS cs (replicate n v)

--------------------------------------------------------------------------------
-- Group
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup "FS.Stream"
    [ ("prop_emit", prop_emit)
    , ("prop_emits", prop_emits)
    , ("prop_emitsChunks", prop_emitsChunks)
    , ("prop_unfoldChunk", prop_unfoldChunk)
    , ("prop_unfold", prop_unfold)
    , ("prop_unfoldAsChunks", prop_unfoldAsChunks)
    , ("prop_constant", prop_constant)
    , ("prop_constantChunks", prop_constantChunks)
    , ("prop_iterate", prop_iterate)
    , ("prop_iterateChunks", prop_iterateChunks)
    , ("prop_fromChunks", prop_fromChunks)
    , ("prop_cons", prop_cons)
    , ("prop_cons1", prop_cons1)
    , ("prop_append", prop_append)
    , ("prop_take", prop_take)
    , ("prop_replicate", prop_replicate)
    , ("prop_replicateChunks", prop_replicateChunks)
    ]
