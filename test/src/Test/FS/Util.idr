module Test.FS.Util

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
