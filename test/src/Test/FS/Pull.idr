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

prop_uncons_pure : Property
prop_uncons_pure =
  property $ do
    v <- forAll bytes
    res (map fst <$> uncons {q = Void, o = Void} (pure v)) === succ (Left v) []

prop_uncons_emit : Property
prop_uncons_emit =
  property $ do
    v <- forAll bytes
    res (map fst <$> uncons {q = Void} (emit v)) === succ (Right v) []

prop_uncons_rem : Property
prop_uncons_rem =
  property $ do
    [v,vs] <- forAll $ hlist [bytes, byteLists]
    res (pll v vs) === succ v vs

  where
    pll : Bits8 -> List Bits8 -> Pull (Elin s) Bits8 [] Bits8
    pll v vs = do
      Right (x,rem) <- uncons (cons v $ emits vs) | Left _ => pure v
      rem $> x

prop_take : Property
prop_take =
  property $ do
    [n, vs] <- forAll $ hlist [smallNats, byteLists]
    res (take n (emits vs)) === out (take n vs)

prop_takeWhile : Property
prop_takeWhile =
  property $ do
    [v, vs] <- forAll $ hlist [bytes, byteLists]
    res (takeWhile (v <) (emits vs)) === out (takeWhile (v <) vs)

prop_sum : Property
prop_sum =
  property $ do
    vs <- forAll byteLists
    res (sum (emits vs)) === out [sum vs]

prop_count : Property
prop_count =
  property $ do
    vs <- forAll byteLists
    res (count (emits vs)) === out [length vs]

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
    , ("prop_uncons_pure", prop_uncons_pure)
    , ("prop_uncons_emit", prop_uncons_emit)
    , ("prop_uncons_rem", prop_uncons_rem)
    , ("prop_take", prop_take)
    , ("prop_takeWhile", prop_takeWhile)
    , ("prop_sum", prop_sum)
    , ("prop_count", prop_count)
     ]
