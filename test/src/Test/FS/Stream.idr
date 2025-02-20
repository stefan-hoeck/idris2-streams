module Test.FS.Stream

import Control.Monad.Elin
import FS.Stream
import Test.FS.Util

%default total

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
echunks : (forall s . Stream (Elin s) es o) -> Result es (List $ List o)
echunks p = runElin (toChunks p)

||| Like `echunks`, but without the possibility of failure.
export
chunks : (forall s . Stream (Elin s) [] o) -> List (List o)
chunks p = either absurd id $ echunks p

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
    chunks (emits vs) === nonEmpty [vs]

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
    ]
