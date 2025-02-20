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
    ]
