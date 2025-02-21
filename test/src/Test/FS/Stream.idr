module Test.FS.Stream

import Control.Monad.Elin
import Data.Linear.Traverse1
import Data.List
import Data.SnocList
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

export
testStream : Show o => (forall s . Stream (Elin s) [] o) -> IO ()
testStream = printLn . runStream

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

prop_takeRight : Property
prop_takeRight =
  property $ do
    [n, vss] <- forAll $ hlist [smallNats, byteChunks]
    runStream (takeRight (S n) (fromChunks vss)) ===
      reverse (take (S n) . reverse $ join vss)

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

prop_drop : Property
prop_drop =
  property $ do
    [n, vss] <- forAll $ hlist [smallNats, byteChunks]
    runStream (drop n (fromChunks vss)) === drop n (join vss)

prop_takeWhile : Property
prop_takeWhile =
  property $ do
    vss <- forAll byteChunks
    runStream (takeWhile (< 100) (fromChunks vss)) === takeWhile (< 100) (join vss)

prop_takeWhileTrue : Property
prop_takeWhileTrue =
  property $ do
    vss <- forAll byteChunks
    schunks (takeWhile (const True) (fromChunks vss)) === nonEmpty vss

prop_takeWhileFalse : Property
prop_takeWhileFalse =
  property $ do
    vss <- forAll byteChunks
    schunks (takeWhile (const False) (fromChunks vss)) === []

prop_takeThroughTrue : Property
prop_takeThroughTrue =
  property $ do
    vss <- forAll byteChunks
    schunks (takeThrough (const True) (fromChunks vss)) === nonEmpty vss

prop_takeThroughFalse : Property
prop_takeThroughFalse =
  property $ do
    vss <- forAll byteChunks
    schunks (takeThrough (const False) (fromChunks vss)) === firstl vss

prop_dropWhile : Property
prop_dropWhile =
  property $ do
    vss <- forAll byteChunks
    runStream (dropWhile (< 100) (fromChunks vss)) === dropWhile (< 100) (join vss)

prop_dropWhileTrue : Property
prop_dropWhileTrue =
  property $ do
    vss <- forAll byteChunks
    schunks (dropWhile (const True) (fromChunks vss)) === []

prop_dropWhileFalse : Property
prop_dropWhileFalse =
  property $ do
    vss <- forAll byteChunks
    schunks (dropWhile (const False) (fromChunks vss)) === nonEmpty vss

prop_dropThroughTrue : Property
prop_dropThroughTrue =
  property $ do
    vss <- forAll byteChunks
    schunks (dropThrough (const True) (fromChunks vss)) === []

prop_dropThroughFalse : Property
prop_dropThroughFalse =
  property $ do
    vss <- forAll byteChunks
    runStream (dropThrough (const False) (fromChunks vss)) === drop 1 (join vss)

prop_find : Property
prop_find =
  property $ do
    vss <- forAll byteChunks
    runStream (find (> 10) (fromChunks vss)) === toList (find (> 10) $ join vss)

prop_mapChunksId : Property
prop_mapChunksId =
  property $ do
    vss <- forAll byteChunks
    schunks (mapChunks id (fromChunks vss)) === nonEmpty vss

prop_mapChunksConst : Property
prop_mapChunksConst =
  property $ do
    [n,vss] <- forAll $ hlist [smallNats, byteChunks]
    schunks (mapChunks (const [n]) (fromChunks vss)) ===
      map (const [n]) (nonEmpty vss)

prop_drain : Property
prop_drain =
  property $ do
    vss <- forAll byteChunks
    schunks (drain {q = Nat} (fromChunks vss)) === []

prop_filter : Property
prop_filter =
  property $ do
    vss <- forAll byteChunks
    schunks (filter (> 3) (fromChunks vss)) === nonEmpty (filter (> 3) <$> vss)

prop_filterNot : Property
prop_filterNot =
  property $ do
    vss <- forAll byteChunks
    schunks (filterNot (> 3) (fromChunks vss)) === nonEmpty (filter (<= 3) <$> vss)

prop_unfoldEval : Property
prop_unfoldEval =
  property $ do
    vs <- forAll byteLists
    runStream (evalFromList vs) === vs

prop_unfoldEvalChunk : Property
prop_unfoldEvalChunk =
  property $ do
    vss <- forAll byteChunks
    schunks (evalFromChunks vss) === nonEmpty vss

prop_evalMap : Property
prop_evalMap =
  property $ do
    vss <- forAll byteChunks
    runStream (zipIx1 $ fromChunks vss) === zipWithIndex (join vss)

prop_evalMapPure : Property
prop_evalMapPure =
  property $ do
    vss <- forAll byteChunks
    runStream (evalMap pure $ fromChunks vss) === join vss

prop_evalMapChunk : Property
prop_evalMapChunk =
  property $ do
    vss <- forAll byteChunks
    runStream (zipIx $ fromChunks vss) === zipWithIndex (join vss)

prop_evalMapChunkPure : Property
prop_evalMapChunkPure =
  property $ do
    vss <- forAll byteChunks
    runStream (evalMapChunk pure $ fromChunks vss) === join vss

prop_foldChunks : Property
prop_foldChunks =
  property $ do
    vss <- forAll byteChunks
    runStream (foldChunks (the Bits8 0) (\n => (n+) . sum) (fromChunks vss)) ===
      [sum $ join vss]

prop_fold : Property
prop_fold =
  property $ do
    vss <- forAll byteChunks
    runStream (fold 0 (+) (fromChunks vss)) === [sum $ join vss]

prop_fold1 : Property
prop_fold1 =
  property $ do
    vss <- forAll byteChunks
    runStream (fold1 max $ fromChunks vss) === fold1s max vss

prop_foldMap : Property
prop_foldMap =
  property $ do
    vss <- forAll byteChunks
    runStream (foldMap ([<]:<) $ fromChunks vss) === [[<] <>< join vss]

prop_concat : Property
prop_concat =
  property $ do
    vss <- forAll byteChunks
    runStream (concat . map ([<]:<) $ fromChunks vss) === [[<] <>< join vss]

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
    , ("prop_takeRight", prop_takeRight)
    , ("prop_replicate", prop_replicate)
    , ("prop_replicateChunks", prop_replicateChunks)
    , ("prop_drop", prop_drop)
    , ("prop_takeWhile", prop_takeWhile)
    , ("prop_takeWhileTrue", prop_takeWhileTrue)
    , ("prop_takeWhileFalse", prop_takeWhileFalse)
    , ("prop_takeThroughTrue", prop_takeThroughTrue)
    , ("prop_takeThroughFalse", prop_takeThroughFalse)
    , ("prop_dropWhile", prop_dropWhile)
    , ("prop_dropWhileTrue", prop_dropWhileTrue)
    , ("prop_dropWhileFalse", prop_dropWhileFalse)
    , ("prop_dropThroughTrue", prop_dropThroughTrue)
    , ("prop_dropThroughFalse", prop_dropThroughFalse)
    , ("prop_find", prop_find)
    , ("prop_mapChunksId", prop_mapChunksId)
    , ("prop_mapChunksConst", prop_mapChunksConst)
    , ("prop_drain", prop_drain)
    , ("prop_filter", prop_filter)
    , ("prop_filterNot", prop_filterNot)
    , ("prop_unfoldEval", prop_unfoldEval)
    , ("prop_unfoldEvalChunk", prop_unfoldEvalChunk)
    , ("prop_evalMap", prop_evalMap)
    , ("prop_evalMapPure", prop_evalMapPure)
    , ("prop_evalMapChunk", prop_evalMapChunk)
    , ("prop_evalMapChunkPure", prop_evalMapChunkPure)
    , ("prop_foldChunks", prop_foldChunks)
    , ("prop_fold", prop_fold)
    , ("prop_fold1", prop_fold1)
    , ("prop_foldMap", prop_foldMap)
    , ("prop_concat", prop_concat)
    ]
