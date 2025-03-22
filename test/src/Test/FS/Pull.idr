module Test.FS.Pull

import Data.Linear.Ref1
import Data.List
import Data.Maybe
import Data.SnocList

import FS.Elin as E

import public Test.FS.Util

--------------------------------------------------------------------------------
-- Effectful utilities
--------------------------------------------------------------------------------

add1 : Bits8 -> Elin s es Bits8
add1 n = do
  ref <- newref n
  mod ref (+1)
  readref ref

nextVal : List a -> UnfoldRes () (List a) a
nextVal []     = Done ()
nextVal [h]    = Last () h
nextVal (h::t) = More h t

nextEval : List Bits8 -> Elin s es (UnfoldRes () (List Bits8) Bits8)
nextEval []     = pure $ Done ()
nextEval [h]    = Last () <$> add1 h
nextEval (h::t) = (`More` t) <$> add1 h

nextMaybe : Ref s (List a) -> Elin s es (Maybe a)
nextMaybe ref = do
  h::t <- readref ref | [] => pure Nothing
  writeref ref t
  pure (Just h)

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_pure : Property
prop_pure =
  property $ do
    v <- forAll bytes
    res (pure v) === succ v {o = Void} []

prop_throw : Property
prop_throw =
  property $ do
    v <- forAll bytes
    resErrs [Bits8] (throw v) === failed (Here v) {r = Void, o = Void} []

prop_exec : Property
prop_exec =
  property $ do
    v <- forAll bytes
    res (newref v >>= exec . readref) === succ v {o = Void} []

prop_emit : Property
prop_emit =
  property $ do
    v <- forAll bytes
    res (emit v) === out [v]

prop_emits : Property
prop_emits =
  property $ do
    vs <- forAll byteLists
    res (emits vs) === out vs

prop_emitList : Property
prop_emitList =
  property $ do
    vs <- forAll byteLists
    case vs of
      [] => res (emitList vs) === out []
      xs => res (emitList vs) === out [vs]

prop_emitMaybe : Property
prop_emitMaybe =
  property $ do
    vs <- forAll (maybe bytes)
    res (emitMaybe vs) === out (toList vs)

prop_eval : Property
prop_eval =
  property $ do
    v <- forAll bytes
    res (eval $ add1 v) === out [v+1]

prop_unfold : Property
prop_unfold =
  property $ do
    vs <- forAll byteLists
    res (unfold vs nextVal) === out vs

prop_unfoldEval : Property
prop_unfoldEval =
  property $ do
    vs <- forAll byteLists
    res (unfoldEval vs nextEval) === out (map (+1) vs)

prop_unfoldEvalMaybe : Property
prop_unfoldEvalMaybe =
  property $ do
    vs <- forAll byteLists
    res (exec (newref vs) >>= unfoldEvalMaybe . nextMaybe) === out vs

prop_fill : Property
prop_fill =
  property $ do
    [n,v] <- forAll $ hlist [smallNats, bytes]
    res (take n $ fill v) === out (replicate n v)

prop_iterate : Property
prop_iterate =
  property $ do
    n <- forAll posNats
    res (take n $ iterate 0 S) === out [0..pred n]

prop_replicate : Property
prop_replicate =
  property $ do
    [n,v] <- forAll $ hlist [smallNats, bytes]
    res (replicate n v) === out (replicate n v)

prop_cons : Property
prop_cons =
  property $ do
    [v,vs] <- forAll $ hlist [bytes,byteLists]
    res (cons v $ emits vs) === out (v::vs)

prop_consMaybe : Property
prop_consMaybe =
  property $ do
    [v,vs] <- forAll $ hlist [maybe bytes,byteLists]
    res (consMaybe v $ emits vs) === out (toList v ++ vs)

-- prop_uncons : Property
-- prop_uncons =
--   property $ do
--     vss <- forAll byteChunks
--     pullChunks (uncons (fromChunks vss) >>= headOut) === firstNotNull vss
--
-- prop_unconsrem : Property
-- prop_unconsrem =
--   property $ do
--     vss <- forAll byteChunks
--     pullChunks (uncons (fromChunks vss) >>= tailOut) === drop 1 (nonEmpty vss)
--
-- prop_uncons1 : Property
-- prop_uncons1 =
--   property $ do
--     vss <- forAll byteChunks
--     pullChunks (uncons1 (fromChunks vss) >>= headOut1) === firstl vss
--
-- prop_unconsLimit : Property
-- prop_unconsLimit =
--   property $ do
--     [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
--     let res := pullChunks (unconsLimit n (fromChunks vss) >>= headOut)
--     case nonEmpty vss of
--       h::_ => res === [take n h]
--       _    => res === []
--
-- prop_unconsMinFalse : Property
-- prop_unconsMinFalse =
--   property $ do
--     [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
--     let res := pullList (unconsMin n False (fromChunks vss) >>= headOut)
--         all := concat vss
--     case length all >= n of
--       True  => assert (isPrefixOf res all && length res >= n)
--       False => res === []
--
-- prop_unconsMinTrue : Property
-- prop_unconsMinTrue =
--   property $ do
--     [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
--     let res := pullList (unconsMin n True (fromChunks vss) >>= headOut)
--         all := concat vss
--     case length all >= n of
--       True  => assert (isPrefixOf res all && length res >= n)
--       False => res === all
--
-- prop_unconsNFalse : Property
-- prop_unconsNFalse =
--   property $ do
--     [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
--     let res := pullList (unconsN n False (fromChunks vss) >>= headOut)
--         all := concat vss
--     case length all >= n of
--       True  => assert (isPrefixOf res all && length res == n)
--       False => res === []
--
-- prop_unconsNTrue : Property
-- prop_unconsNTrue =
--   property $ do
--     [CS n, vss] <- forAll $ hlist [chunkSizes, byteChunks]
--     let res := pullList (unconsN n True (fromChunks vss) >>= headOut)
--         all := concat vss
--     case length all >= n of
--       True  => assert (isPrefixOf res all && length res == n)
--       False => res === all
--
-- prop_take : Property
-- prop_take =
--   property $ do
--     [n, vss] <- forAll $ hlist [smallNats, byteChunks]
--     pullList (ignore $ take n (fromChunks vss)) === take n (join vss)
--
-- prop_takerem : Property
-- prop_takerem =
--   property $ do
--     [n, vss] <- forAll $ hlist [smallNats, byteChunks]
--     pullList (take n (fromChunks vss) >>= orEmpty) === join vss
--
-- prop_takeRight : Property
-- prop_takeRight =
--   property $ do
--     [n, vss] <- forAll $ hlist [smallNats, byteChunks]
--     pullList (takeRight (S n) (fromChunks vss) >>= output) ===
--       reverse (take (S n) . reverse $ join vss)
--
-- prop_last : Property
-- prop_last =
--   property $ do
--     vss <- forAll byteChunks
--     pullList (last (fromChunks vss) >>= traverse_ output1) === lastl (join vss)
--
-- prop_peek : Property
-- prop_peek =
--   property $ do
--     vss <- forAll byteChunks
--     pullChunks (peek (fromChunks vss) >>= headOut) === firstNotNull vss
--
-- prop_peekrem : Property
-- prop_peekrem =
--   property $ do
--     vss <- forAll byteChunks
--     pullChunks (peek (fromChunks vss) >>= tailOut) === nonEmpty vss
--
-- prop_peek1 : Property
-- prop_peek1 =
--   property $ do
--     vss <- forAll byteChunks
--     pullChunks (peek1 (fromChunks vss) >>= headOut1) === firstl vss
--
-- prop_peek1rem : Property
-- prop_peek1rem =
--   property $ do
--     vss <- forAll byteChunks
--     pullChunks (peek1 (fromChunks vss) >>= tailOut) === nonEmpty vss
--
-- prop_takeWhileRem : Property
-- prop_takeWhileRem =
--   property $ do
--     vss <- forAll byteChunks
--     pullList (takeWhile (< 10) (fromChunks vss) >>= orEmpty) ===
--       join vss
--
-- prop_takeThroughRem : Property
-- prop_takeThroughRem =
--   property $ do
--     vss <- forAll byteChunks
--     pullList (takeThrough (< 10) (fromChunks vss) >>= orEmpty) ===
--       join vss
--
-- prop_find : Property
-- prop_find =
--   property $ do
--     vss <- forAll byteChunks
--     pullList (find (> 10) (fromChunks vss) >>= emitBoth1) ===
--       dropWhile (<= 10) (join vss)
--
-- prop_foldChunks : Property
-- prop_foldChunks =
--   property $ do
--     vss <- forAll byteChunks
--     pullList (foldChunks (the Bits8 0) (\n => (n+) . sum) (fromChunks vss) >>= output1) ===
--       [sum $ join vss]
--
-- prop_fold : Property
-- prop_fold =
--   property $ do
--     vss <- forAll byteChunks
--     pullList (fold 0 (+) (fromChunks vss) >>= output1) === [sum $ join vss]
--
--------------------------------------------------------------------------------
-- Group
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup "FS.Pull"
    [ ("prop_pure", prop_pure)
    , ("prop_throw", prop_throw)
    , ("prop_exec", prop_exec)
    , ("prop_emit", prop_emit)
    , ("prop_emits", prop_emits)
    , ("prop_emitList", prop_emitList)
    , ("prop_emitMaybe", prop_emitMaybe)
    , ("prop_eval", prop_eval)
    , ("prop_unfold", prop_unfold)
    , ("prop_unfoldEval", prop_unfoldEval)
    , ("prop_unfoldEvalMaybe", prop_unfoldEvalMaybe)
    , ("prop_fill", prop_fill)
    , ("prop_iterate", prop_iterate)
    , ("prop_replicate", prop_replicate)
    , ("prop_cons", prop_cons)
    , ("prop_consMaybe", prop_consMaybe)
--     , ("prop_uncons", prop_uncons)
--     , ("prop_unconsrem", prop_unconsrem)
--     , ("prop_uncons1", prop_uncons1)
--     , ("prop_unconsLimit", prop_unconsLimit)
--     , ("prop_unconsMinFalse", prop_unconsMinFalse)
--     , ("prop_unconsMinTrue", prop_unconsMinTrue)
--     , ("prop_unconsNFalse", prop_unconsNFalse)
--     , ("prop_unconsNTrue", prop_unconsNTrue)
--     , ("prop_take", prop_take)
--     , ("prop_takerem", prop_takerem)
--     , ("prop_takeRight", prop_takeRight)
--     , ("prop_takeWhileRem", prop_takeWhileRem)
--     , ("prop_takeThroughRem", prop_takeThroughRem)
--     , ("prop_last", prop_last)
--     , ("prop_peek", prop_peek)
--     , ("prop_peekrem", prop_peekrem)
--     , ("prop_peek1", prop_peek1)
--     , ("prop_peek1rem", prop_peek1rem)
--     , ("prop_find", prop_find)
--     , ("prop_foldChunks", prop_foldChunks)
--     , ("prop_fold", prop_fold)
     ]
