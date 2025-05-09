module Test.FS.Stream

import Control.Monad.Elin
import Data.Linear.Traverse1
import Data.List
import Data.SnocList
import FS.Pull
import FS.Stream
import Test.FS.Util

-- --------------------------------------------------------------------------------
-- -- Properties
-- --------------------------------------------------------------------------------
--
-- prop_emit : Property
-- prop_emit =
--   property $ do
--     v <- forAll bytes
--     streamList (emit v) === [v]
--
-- prop_emits : Property
-- prop_emits =
--   property $ do
--     vs <- forAll byteLists
--     streamList (emits vs) === vs
--
-- prop_emitsChunks : Property
-- prop_emitsChunks =
--   property $ do
--     vs <- forAll byteLists
--     streamChunks (emits vs) === nonEmpty [vs]
--
-- prop_unfoldChunk : Property
-- prop_unfoldChunk =
--   property $ do
--     n <- forAll posNats
--     streamChunks (unfoldChunk n next) === map (\x => replicate x x) [n..1]
--
--   where
--     next : Nat -> (List Nat, Maybe Nat)
--     next 0       = ([], Nothing)
--     next n@(S k) = (replicate n n, Just k)
--
-- prop_unfold : Property
-- prop_unfold =
--   property $ do
--     n <- forAll posNats
--     streamList (unfold n next) === map (\x => x * x) [n..1]
--   where
--     next : Nat -> Maybe (Nat,Nat)
--     next 0       = Nothing
--     next n@(S k) = Just (n*n,k)
--
-- prop_unfoldAsChunks : Property
-- prop_unfoldAsChunks =
--   property $ do
--     [cs,n] <- forAll $ hlist [chunkSizes, posNats]
--     streamChunks (unfold @{cs} n next) === chunkedCS cs (map (\x => x * x) [n..1])
--   where
--     next : Nat -> Maybe (Nat,Nat)
--     next 0       = Nothing
--     next n@(S k) = Just (n*n,k)
--
-- prop_constant : Property
-- prop_constant =
--   property $ do
--     [n,v] <- forAll $ hlist [smallNats, bytes]
--     streamList (take n $ constant v) === replicate n v
--
-- prop_constantChunks : Property
-- prop_constantChunks =
--   property $ do
--     [cs, n,v] <- forAll $ hlist [chunkSizes, smallNats, bytes]
--     streamChunks (take n $ constant @{cs} v) === chunkedCS cs (replicate n v)
--
-- prop_iterate : Property
-- prop_iterate =
--   property $ do
--     n <- forAll posNats
--     streamList (take n $ iterate 0 S) === [0..pred n]
--
-- prop_iterateChunks : Property
-- prop_iterateChunks =
--   property $ do
--     [cs,n] <- forAll $ hlist [chunkSizes, posNats]
--     streamChunks (take n $ iterate @{cs} 0 S) === chunkedCS cs [0..pred n]
--
-- prop_fromChunks : Property
-- prop_fromChunks =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (fromChunks vss) === filter (not . null) vss
--
-- prop_cons : Property
-- prop_cons =
--   property $ do
--     [vs,vss] <- forAll $ hlist [byteLists, byteChunks]
--     streamChunks (cons vs $ fromChunks vss) === filter (not . null) (vs::vss)
--
-- prop_cons1 : Property
-- prop_cons1 =
--   property $ do
--     [v,vss] <- forAll $ hlist [bytes, byteChunks]
--     streamChunks (cons1 v $ fromChunks vss) === filter (not . null) ([v]::vss)
--
-- prop_append : Property
-- prop_append =
--   property $ do
--     [vss,wss] <- forAll $ hlist [byteChunks, byteChunks]
--     streamChunks (fromChunks vss ++ fromChunks wss) === filter (not . null) (vss++wss)
--
-- prop_take : Property
-- prop_take =
--   property $ do
--     [n, vss] <- forAll $ hlist [smallNats, byteChunks]
--     streamList (take n (fromChunks vss)) === take n (join vss)
--
-- prop_takeRight : Property
-- prop_takeRight =
--   property $ do
--     [n, vss] <- forAll $ hlist [smallNats, byteChunks]
--     streamList (takeRight (S n) (fromChunks vss)) ===
--       reverse (take (S n) . reverse $ join vss)
--
-- prop_replicate : Property
-- prop_replicate =
--   property $ do
--     [n,v] <- forAll $ hlist [smallNats, bytes]
--     streamList (replicate n v) === replicate n v
--
-- prop_replicateChunks : Property
-- prop_replicateChunks =
--   property $ do
--     [cs,n,v] <- forAll $ hlist [chunkSizes, smallNats, bytes]
--     streamChunks (replicate @{cs} n v) === chunkedCS cs (replicate n v)
--
-- prop_drop : Property
-- prop_drop =
--   property $ do
--     [n, vss] <- forAll $ hlist [smallNats, byteChunks]
--     streamList (drop n (fromChunks vss)) === drop n (join vss)
--
-- prop_takeWhile : Property
-- prop_takeWhile =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (takeWhile (< 100) (fromChunks vss)) === takeWhile (< 100) (join vss)
--
-- prop_takeWhileTrue : Property
-- prop_takeWhileTrue =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (takeWhile (const True) (fromChunks vss)) === nonEmpty vss
--
-- prop_takeWhileFalse : Property
-- prop_takeWhileFalse =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (takeWhile (const False) (fromChunks vss)) === []
--
-- prop_takeThroughTrue : Property
-- prop_takeThroughTrue =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (takeThrough (const True) (fromChunks vss)) === nonEmpty vss
--
-- prop_takeThroughFalse : Property
-- prop_takeThroughFalse =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (takeThrough (const False) (fromChunks vss)) === firstl vss
--
-- prop_dropWhile : Property
-- prop_dropWhile =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (dropWhile (< 100) (fromChunks vss)) === dropWhile (< 100) (join vss)
--
-- prop_dropWhileTrue : Property
-- prop_dropWhileTrue =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (dropWhile (const True) (fromChunks vss)) === []
--
-- prop_dropWhileFalse : Property
-- prop_dropWhileFalse =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (dropWhile (const False) (fromChunks vss)) === nonEmpty vss
--
-- prop_dropThroughTrue : Property
-- prop_dropThroughTrue =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (dropThrough (const True) (fromChunks vss)) === []
--
-- prop_dropThroughFalse : Property
-- prop_dropThroughFalse =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (dropThrough (const False) (fromChunks vss)) === drop 1 (join vss)
--
-- prop_find : Property
-- prop_find =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (find (> 10) (fromChunks vss)) === toList (find (> 10) $ join vss)
--
-- prop_mapChunksId : Property
-- prop_mapChunksId =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (mapChunks id (fromChunks vss)) === nonEmpty vss
--
-- prop_mapChunksConst : Property
-- prop_mapChunksConst =
--   property $ do
--     [n,vss] <- forAll $ hlist [smallNats, byteChunks]
--     streamChunks (mapChunks (const [n]) (fromChunks vss)) ===
--       map (const [n]) (nonEmpty vss)
--
-- prop_drain : Property
-- prop_drain =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (drain {q = Nat} (fromChunks vss)) === []
--
-- prop_filter : Property
-- prop_filter =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (filter (> 3) (fromChunks vss)) === nonEmpty (filter (> 3) <$> vss)
--
-- prop_filterNot : Property
-- prop_filterNot =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (filterNot (> 3) (fromChunks vss)) === nonEmpty (filter (<= 3) <$> vss)
--
-- prop_unfoldEval : Property
-- prop_unfoldEval =
--   property $ do
--     vs <- forAll byteLists
--     streamList (evalFromList vs) === vs
--
-- prop_unfoldEvalChunk : Property
-- prop_unfoldEvalChunk =
--   property $ do
--     vss <- forAll byteChunks
--     streamChunks (evalFromChunks vss) === nonEmpty vss
--
-- prop_evalMap : Property
-- prop_evalMap =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (zipIx1 $ fromChunks vss) === zipWithIndex (join vss)
--
-- prop_evalMapPure : Property
-- prop_evalMapPure =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (evalMap pure $ fromChunks vss) === join vss
--
-- prop_evalMapChunk : Property
-- prop_evalMapChunk =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (zipIx $ fromChunks vss) === zipWithIndex (join vss)
--
-- prop_evalMapChunkPure : Property
-- prop_evalMapChunkPure =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (evalMapChunk pure $ fromChunks vss) === join vss
--
-- prop_foldChunks : Property
-- prop_foldChunks =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (foldChunks (the Bits8 0) (\n => (n+) . sum) (fromChunks vss)) ===
--       [sum $ join vss]
--
-- prop_fold : Property
-- prop_fold =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (fold 0 (+) (fromChunks vss)) === [sum $ join vss]
--
-- prop_fold1 : Property
-- prop_fold1 =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (fold1 max $ fromChunks vss) === fold1s max vss
--
-- prop_foldMap : Property
-- prop_foldMap =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (foldMap ([<]:<) $ fromChunks vss) === [[<] <>< join vss]
--
-- prop_concat : Property
-- prop_concat =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (concat . map ([<]:<) $ fromChunks vss) === [[<] <>< join vss]
--
-- prop_zipWith : Property
-- prop_zipWith =
--   property $ do
--     [vss,wss] <- forAll $ hlist [byteChunks, byteChunks]
--     streamList (zipWith (+) (fromChunks vss) (fromChunks wss)) ===
--       zipWith (+) (join vss) (join wss)
--
-- prop_zip : Property
-- prop_zip =
--   property $ do
--     [vss,wss] <- forAll $ hlist [byteChunks, byteChunks]
--     streamList (zip (fromChunks vss) (fromChunks wss)) ===
--       zip (join vss) (join wss)
--
-- prop_padLeft : Property
-- prop_padLeft =
--   property $ do
--     [v,vss] <- forAll $ hlist [bytes, byteChunks]
--     streamList (zipAll v v neutral (fromChunks vss)) === map (v,) (join vss)
--
-- prop_padRight : Property
-- prop_padRight =
--   property $ do
--     [v,vss] <- forAll $ hlist [bytes, byteChunks]
--     streamList (zipAll v v (fromChunks vss) neutral) === map (,v) (join vss)
--
-- prop_zipWithIndex : Property
-- prop_zipWithIndex =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (zipWithIndex $ fromChunks vss) ===
--       (swap <$> zipWithIndex (join vss))
--
-- prop_zipWithScan1 : Property
-- prop_zipWithScan1 =
--   property $ do
--     vss <- forAll byteChunks
--     streamList (zipWithScan1 0 (\n,_ => S n) $ fromChunks vss) ===
--       ((\(n,v) => (v, S n)) <$> zipWithIndex (join vss))
--
-- prop_zipWithPrevious : Property
-- prop_zipWithPrevious =
--   property $ do
--     vss <- forAll byteChunks
--     let vs := join vss
--         tl := maybe [] ((Nothing ::) . map Just) (init' vs)
--     streamList (zipWithPrevious $ fromChunks vss) === zip tl vs
--
-- prop_intersperse : Property
-- prop_intersperse =
--   property $ do
--     [v,vss] <- forAll $ hlist [bytes, byteChunks]
--     streamList (intersperse v $ fromChunks vss) === intersperse v (join vss)
--
-- --------------------------------------------------------------------------------
-- -- Group
-- --------------------------------------------------------------------------------
--
-- export
-- props : Group
-- props =
--   MkGroup "FS.Stream"
--     [ ("prop_emit", prop_emit)
--     , ("prop_emits", prop_emits)
--     , ("prop_emitsChunks", prop_emitsChunks)
--     , ("prop_unfoldChunk", prop_unfoldChunk)
--     , ("prop_unfold", prop_unfold)
--     , ("prop_unfoldAsChunks", prop_unfoldAsChunks)
--     , ("prop_constant", prop_constant)
--     , ("prop_constantChunks", prop_constantChunks)
--     , ("prop_iterate", prop_iterate)
--     , ("prop_iterateChunks", prop_iterateChunks)
--     , ("prop_fromChunks", prop_fromChunks)
--     , ("prop_cons", prop_cons)
--     , ("prop_cons1", prop_cons1)
--     , ("prop_append", prop_append)
--     , ("prop_take", prop_take)
--     , ("prop_takeRight", prop_takeRight)
--     , ("prop_replicate", prop_replicate)
--     , ("prop_replicateChunks", prop_replicateChunks)
--     , ("prop_drop", prop_drop)
--     , ("prop_takeWhile", prop_takeWhile)
--     , ("prop_takeWhileTrue", prop_takeWhileTrue)
--     , ("prop_takeWhileFalse", prop_takeWhileFalse)
--     , ("prop_takeThroughTrue", prop_takeThroughTrue)
--     , ("prop_takeThroughFalse", prop_takeThroughFalse)
--     , ("prop_dropWhile", prop_dropWhile)
--     , ("prop_dropWhileTrue", prop_dropWhileTrue)
--     , ("prop_dropWhileFalse", prop_dropWhileFalse)
--     , ("prop_dropThroughTrue", prop_dropThroughTrue)
--     , ("prop_dropThroughFalse", prop_dropThroughFalse)
--     , ("prop_find", prop_find)
--     , ("prop_mapChunksId", prop_mapChunksId)
--     , ("prop_mapChunksConst", prop_mapChunksConst)
--     , ("prop_drain", prop_drain)
--     , ("prop_filter", prop_filter)
--     , ("prop_filterNot", prop_filterNot)
--     , ("prop_unfoldEval", prop_unfoldEval)
--     , ("prop_unfoldEvalChunk", prop_unfoldEvalChunk)
--     , ("prop_evalMap", prop_evalMap)
--     , ("prop_evalMapPure", prop_evalMapPure)
--     , ("prop_evalMapChunk", prop_evalMapChunk)
--     , ("prop_evalMapChunkPure", prop_evalMapChunkPure)
--     , ("prop_foldChunks", prop_foldChunks)
--     , ("prop_fold", prop_fold)
--     , ("prop_fold1", prop_fold1)
--     , ("prop_foldMap", prop_foldMap)
--     , ("prop_concat", prop_concat)
--     , ("prop_zip", prop_zip)
--     , ("prop_zipWith", prop_zipWith)
--     , ("prop_padLeft", prop_padLeft)
--     , ("prop_padRight", prop_padRight)
--     , ("prop_zipWithIndex", prop_zipWithIndex)
--     , ("prop_zipWithScan1", prop_zipWithScan1)
--     , ("prop_zipWithPrevious", prop_zipWithPrevious)
--     , ("prop_intersperse", prop_intersperse)
--     ]
