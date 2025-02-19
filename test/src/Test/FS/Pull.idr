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

prop_unfoldChunksLeft : Property
prop_unfoldChunksLeft =
  property $ do
    vs <- forAll byteLists
    let cs := chunks $ unfoldChunk () (const (vs, Left ()))
    case vs of
      [] => cs === []
      _  => cs === [vs]

prop_unfoldChunks : Property
prop_unfoldChunks =
  property $ do
    n <- forAll posNats
    chunks (unfoldChunk n next) === map (\x => replicate x x) [n..1]

  where
    next : Nat -> (List Nat, Either () Nat)
    next 0       = ([], Left ())
    next n@(S k) = (replicate n n, Right k)

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
    [cs@(CS sz),n] <- forAll $ hlist [chunkSizes, posNats]
    chunks (unfold @{cs} n next) === chunked sz (map (\x => x * x) [n..1])
  where
    next : Nat -> Either () (Nat,Nat)
    next 0       = Left ()
    next n@(S k) = Right (n*n,k)

export
props : Group
props =
  MkGroup "FS.Pull"
    [ ("prop_output1", prop_output1)
    , ("prop_output", prop_output)
    , ("prop_outputChunks", prop_outputChunks)
    , ("prop_foldable", prop_foldable)
    , ("prop_unfoldChunksLeft", prop_unfoldChunksLeft)
    , ("prop_unfoldChunks", prop_unfoldChunks)
    , ("prop_unfold", prop_unfold)
    , ("prop_unfoldAsChunks", prop_unfoldAsChunks)
    ]
