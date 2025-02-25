module FS.ChunkSize

import public Data.Nat

%default total

--------------------------------------------------------------------------------
-- Chunk Size
--------------------------------------------------------------------------------

||| Pulls and streams produce their output in chunks (lists of value)
||| for reasons of efficiency, because the whole streaming machinery
||| comes with quite a bit of a performance overhead.
|||
||| Many functions for generating pure streams
||| and pulls therefore take an auto-implicit value of type `ChunkSize`.
||| If not provided explicitly, this defaults to 128.
public export
record ChunkSize where
  [noHints]
  constructor CS
  size        : Nat
  {auto 0 prf : IsSucc size}

export %inline
Eq ChunkSize where
  CS x == CS y = x == y

export %inline
Ord ChunkSize where
  compare (CS x) (CS y) = compare x y

export %inline
Show ChunkSize where
  show = show . size

export
fromInteger : (n : Integer) -> ChunkSize
fromInteger n =
  case cast {to = Nat} n of
    k@(S _) => CS k
    0       => CS 1

public export %inline %hint
defaultChunkSize : ChunkSize
defaultChunkSize = 128
