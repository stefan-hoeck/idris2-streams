module Test.FS.Pull

import Control.Monad.Elin
import Data.List
import Data.SnocList
import FS.Internal.Chunk
import FS.Pull

import public Test.FS.Util

||| Runs a `Pull` to completion, collecting all output in a list.
export
runEPull : (forall s . Pull (Elin s) o es ()) -> Result es (List o)
runEPull p = pullElin ((<>> []) <$> foldChunks [<] (<><) p)

||| Like `runEPull`, but without the possibility of failure.
export
runPull : (forall s . Pull (Elin s) o [] ()) -> List o
runPull p = either absurd id $ runEPull p

||| Runs a `Pull` to completion, collecting all chunks of output in a list.
||| This allows us to observe the chunk structure of a `Pull`.
export
echunks : (forall s . Pull (Elin s) o es ()) -> Result es (List $ List o)
echunks p = pullElin ((<>> []) <$> foldChunks [<] (:<) p)

||| Like `echunks`, but without the possibility of failure.
export
chunks : (forall s . Pull (Elin s) o [] ()) -> List (List o)
chunks p = either absurd id $ echunks p

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_output1 : Property
prop_output1 =
  property $ do
    v <- forAll bytes
    runPull (output1 v) === [v]

prop_output : Property
prop_output =
  property $ do
    vs <- forAll byteLists
    runPull (output vs) === vs

prop_outputChunks : Property
prop_outputChunks =
  property $ do
    vs <- forAll byteLists
    case vs of
      [] => chunks (output vs) === []
      _  => chunks (output vs) === [vs]

prop_foldable : Property
prop_foldable =
  property $ do
    sv <- forAll byteSnocLists
    runPull (foldable sv) === (sv <>> [])

prop_unfoldChunkLeft : Property
prop_unfoldChunkLeft =
  property $ do
    vs <- forAll byteLists
    let cs := chunks $ unfoldChunk () (const (vs, Left ()))
    case vs of
      [] => cs === []
      _  => cs === [vs]

prop_unfoldChunk : Property
prop_unfoldChunk =
  property $ do
    n <- forAll posNats
    chunks (unfoldChunk n next) === map (\x => replicate x x) [n..1]

  where
    next : Nat -> (List Nat, Either () Nat)
    next 0       = ([], Left ())
    next n@(S k) = (replicate n n, Right k)

prop_unfoldChunkMaybe : Property
prop_unfoldChunkMaybe =
  property $ do
    n <- forAll posNats
    chunks (unfoldChunkMaybe n next) === map (\x => replicate x x) [n..1]

  where
    next : Nat -> (List Nat, Maybe Nat)
    next 0       = ([], Nothing)
    next n@(S k) = (replicate n n, Just k)

prop_unfold : Property
prop_unfold =
  property $ do
    n <- forAll posNats
    runPull (unfold n next) === map (\x => x * x) [n..1]
  where
    next : Nat -> Either () (Nat,Nat)
    next 0       = Left ()
    next n@(S k) = Right (n*n,k)

prop_unfoldAsChunks : Property
prop_unfoldAsChunks =
  property $ do
    [cs,n] <- forAll $ hlist [chunkSizes, posNats]
    chunks (unfold @{cs} n next) === chunkedCS cs (map (\x => x * x) [n..1])
  where
    next : Nat -> Either () (Nat,Nat)
    next 0       = Left ()
    next n@(S k) = Right (n*n,k)

prop_unfoldMaybe : Property
prop_unfoldMaybe =
  property $ do
    n <- forAll posNats
    runPull (unfoldMaybe n next) === map (\x => x * x) [n..1]

  where
    next : Nat -> Maybe (Nat,Nat)
    next 0       = Nothing
    next n@(S k) = Just (n*n,k)

prop_unfoldMaybeAsChunks : Property
prop_unfoldMaybeAsChunks =
  property $ do
    [cs,n] <- forAll $ hlist [chunkSizes, posNats]
    chunks (unfoldMaybe @{cs} n next) === chunkedCS cs (map (\x => x * x) [n..1])

  where
    next : Nat -> Maybe (Nat,Nat)
    next 0       = Nothing
    next n@(S k) = Just (n*n,k)

prop_fill : Property
prop_fill =
  property $ do
    [n,v] <- forAll $ hlist [smallNats, bytes]
    runPull (ignore $ take n $ fill v) === replicate n v

prop_fillChunks : Property
prop_fillChunks =
  property $ do
    [cs, n,v] <- forAll $ hlist [chunkSizes, smallNats, bytes]
    chunks (ignore $ take n $ fill @{cs} v) === chunkedCS cs (replicate n v)

prop_iterate : Property
prop_iterate =
  property $ do
    n <- forAll posNats
    runPull (ignore $ take n $ iterate 0 S) === [0..pred n]

prop_iterateChunks : Property
prop_iterateChunks =
  property $ do
    [cs,n] <- forAll $ hlist [chunkSizes, posNats]
    chunks (ignore $ take n $ iterate @{cs} 0 S) === chunkedCS cs [0..pred n]

prop_replicate : Property
prop_replicate =
  property $ do
    [n,v] <- forAll $ hlist [smallNats, bytes]
    runPull (replicate n v) === replicate n v

prop_replicateChunks : Property
prop_replicateChunks =
  property $ do
    [cs,n,v] <- forAll $ hlist [chunkSizes, smallNats, bytes]
    chunks (replicate @{cs} n v) === chunkedCS cs (replicate n v)

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
    ]
