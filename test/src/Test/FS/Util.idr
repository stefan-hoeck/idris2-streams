module Test.FS.Util

import FS.Internal.Chunk
import FS.Pull
import public Hedgehog

%default total

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
chunkedCS (CS sz) = chunked sz

export
lastl : List a -> List a
lastl []     = []
lastl [v]    = [v]
lastl (_::t) = lastl t

export
firstNotNull : List (List a) -> List (List a)
firstNotNull []      = []
firstNotNull ([]::t) = firstNotNull t
firstNotNull (h::t)  = [h]

export
firstl : List (List a) -> List (List a)
firstl vss =
  case firstNotNull vss of
    (h::_)::_ => [[h]]
    _         => []

export
headOut : Foldable m => m (List o, Pull f o es ()) -> Pull f o es ()
headOut ps =
  case toList ps of
    []          => pure ()
    (vs,_) :: _ => output vs

export
tailOut : Foldable m => m (q, Pull f o es ()) -> Pull f o es ()
tailOut ps =
  case toList ps of
    []          => pure ()
    (_,tl) :: _ => tl

export
headOut1 : Foldable m => m (o, Pull f o es ()) -> Pull f o es ()
headOut1 ps =
  case toList ps of
    []         => pure ()
    (v,_) :: _ => output1 v
