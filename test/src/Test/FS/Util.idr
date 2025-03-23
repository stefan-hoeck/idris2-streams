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

--------------------------------------------------------------------------------
-- Results
--------------------------------------------------------------------------------

public export
record Res es o r where
  constructor R
  outcome : Outcome es r
  output  : List o

export
All Show es => Show o => Show r => Show (Res es o r) where
  showPrec p (R o out) = showCon p "R" (showArg o ++ showArg out)

export
All Eq es => Eq o => Eq r => Eq (Res es o r) where
  R oc1 op1 == R oc2 op2 = oc1 == oc2 && op1 == op2

export %inline
succ : r -> List o -> Res es o r
succ = R . Succeeded

export %inline
failed : HSum es -> List o -> Res es o r
failed = R . Error

export %inline
out : List o -> Res es o ()
out = succ ()

export covering
resErrs : (0 es : List Type) -> (forall s . Pull (Elin s) o es r) -> Res es o r
resErrs _ p =
  either absurd id $ runElin $ do
    ref <- newref [<]
    out <- pull $ foreach (\x => mod ref (:< x)) p
    sv  <- readref ref
    pure (R out $ sv <>> [])

export covering %inline
res : (forall s . Pull (Elin s) o [] r) -> Res [] o r
res = resErrs []
