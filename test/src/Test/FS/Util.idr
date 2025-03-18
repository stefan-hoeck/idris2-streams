module Test.FS.Util

import public FS.Elin
import public Hedgehog
import Data.Linear.Ref1
import FS

%default total

--------------------------------------------------------------------------------
-- Generators
--------------------------------------------------------------------------------

export %inline
bytes : Gen Bits8
bytes = anyBits8

export
byteLists : Gen (List Bits8)
byteLists = list (linear 0 30) bytes

export
byteChunks : Gen (List $ List Bits8)
byteChunks = list (linear 0 20) byteLists

export
nonEmptyByteLists : Gen (List Bits8)
nonEmptyByteLists = list (linear 1 30) bytes

export
byteSnocLists : Gen (SnocList Bits8)
byteSnocLists = ([<] <><) <$> byteLists

export
smallNats : Gen Nat
smallNats = nat (linear 0 20)

export
posNats : Gen Nat
posNats = nat (linear 1 20)

export
chunkSizes : Gen ChunkSize
chunkSizes = (\n => CS (S n)) <$> smallNats

export %inline
chunkedCS : ChunkSize -> List a -> List (List a)
-- chunkedCS (CS sz) = chunked sz

--------------------------------------------------------------------------------
-- List and Chunk Utilities
--------------------------------------------------------------------------------

export
fold1s : (a -> a -> a) -> List (List a) -> List a
fold1s f vs =
  case join vs of
    h::t => [foldl f h t]
    []   => []

||| Removes all empty lists from the given list of lists
export
nonEmpty : List (List a) -> List (List a)
nonEmpty = filter (not . null)

||| Returns the (optional) last element of a list wrapped in a list
export
lastl : List a -> List a
lastl []     = []
lastl [v]    = [v]
lastl (_::t) = lastl t

||| Returns the (optional) first non-empty chunk in a list of chunks.
export
firstNotNull : List (List a) -> List (List a)
firstNotNull []      = []
firstNotNull ([]::t) = firstNotNull t
firstNotNull (h::t)  = [h]

||| Returns the (optional) head of the first non-empty chunk in a list
||| of chunks.
export
firstl : List (List a) -> List (List a)
firstl vss =
  case firstNotNull vss of
    (h::_)::_ => [[h]]
    _         => []

-- ||| Emits the first chunk of data in the given foldable (if any).
-- export
-- headOut : Foldable m => m (List o, Pull f o es ()) -> Pull f o es ()
-- headOut ps =
--   case toList ps of
--     []          => pure ()
--     (vs,_) :: _ => output vs
--
-- ||| Returns the first pull in the given foldable (if any).
-- export
-- tailOut : Foldable m => m (q, Pull f o es ()) -> Pull f o es ()
-- tailOut ps =
--   case toList ps of
--     []          => pure ()
--     (_,tl) :: _ => tl
--
-- ||| Emits the first value in the given foldable (if any).
-- export
-- headOut1 : Foldable m => m (o, Pull f o es ()) -> Pull f o es ()
-- headOut1 ps =
--   case toList ps of
--     []         => pure ()
--     (v,_) :: _ => output1 v
--
-- ||| Returns the wrapped stream or the empty stream in case of a `Nothing`
-- export
-- orEmpty : Monoid r => Maybe (Pull f o e r) ->  Pull f o e r
-- orEmpty = fromMaybe (pure neutral)
--
-- ||| Returns a stream that emits the wrapped values and remainder of
-- ||| the stream.
-- export
-- emitBoth : Maybe (List o,Pull f o es ()) -> Pull f o es ()
-- emitBoth Nothing       = pure ()
-- emitBoth (Just (v,vs)) = output v >> vs
--
-- ||| Returns a stream that emits the wrapped value and remainder of
-- ||| the stream.
-- export
-- emitBoth1 : Maybe (o,Pull f o es ()) -> Pull f o es ()
-- emitBoth1 Nothing       = pure ()
-- emitBoth1 (Just (v,vs)) = output1 v >> vs
--
-- export
-- evalFromList : ELift1 s f => List o -> Stream f es o
-- evalFromList vss = eval (newref vss) >>= unfoldEval . next
--
--   where
--     next : Ref s (List o) -> f es (Maybe o)
--     next ref = do
--       h::t <- readref ref | [] => pure Nothing
--       writeref ref t
--       pure (Just h)
--
-- export
-- evalFromChunks : ELift1 s f => List (List o) -> Stream f es o
-- evalFromChunks vss = eval (newref vss) >>= unfoldEvalChunk . next
--
--   where
--     next : Ref s (List $ List o) -> f es (Maybe $ List o)
--     next ref = do
--       h::t <- readref ref | [] => pure Nothing
--       writeref ref t
--       pure (Just h)
--
-- export
-- zipIx1 : ELift1 s f => Stream f es o -> Stream f es (Nat,o)
-- zipIx1 str = eval (newref Z) >>= flip evalMap str . pair
--   where
--     pair : Ref s Nat -> o -> f es (Nat,o)
--     pair ref v = do
--       n <- readref ref
--       writeref ref (S n)
--       pure (n, v)
--
-- export
-- zipIx : ELift1 s f => Stream f es o -> Stream f es (Nat,o)
-- zipIx str = eval (newref Z) >>= flip evalMapChunk str . traverse . pair
--   where
--     pair : Ref s Nat -> o -> f es (Nat,o)
--     pair ref v = do
--       n <- readref ref
--       writeref ref (S n)
--       pure (n, v)
