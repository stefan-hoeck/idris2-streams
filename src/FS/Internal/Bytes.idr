module FS.Internal.Bytes

import Data.Bits
import Data.ByteString
import Data.ByteVect

%default total

public export
0 SnocBytes : Type
SnocBytes = SnocList ByteString

public export
0 Bytes : Type
Bytes = List ByteString

export
nl : ByteString
nl = singleton 0x0a


ls : SnocBytes -> (n : Nat) -> ByteVect n -> (SnocBytes, ByteString)
ls sb n bs = case breakNL bs of
  MkBreakRes l1 0      b1 _  prf => (sb, BS l1 b1)
  MkBreakRes l1 (S l2) b1 b2 prf =>
    ls (sb :< BS l1 b1) (assert_smaller n l2) (tail b2)

export
splitNL : SnocBytes -> ByteString -> Bytes -> (Bytes, ByteString)
splitNL sx x [] = (sx <>> [], x)
splitNL sx x (BS n bs :: bss) =
  case breakNL bs of
    MkBreakRes l1 0      b1 _  prf => splitNL sx (x <+> BS l1 b1) bss
    MkBreakRes l1 (S l2) b1 b2 prf =>
      let (sx2,x2) := ls (sx :< (x <+> BS l1 b1)) l2 (tail b2)
       in splitNL sx2 x2 bss

namespace UTF8
  ||| The number of continuation bytes following a UTF-8 leading byte.
  |||
  ||| See [Wikipedia](https://en.wikipedia.org/wiki/UTF-8#Description)
  ||| for a description of the magic numbers used in the implementation
  ||| and the UTF-8 encoding in general.
  export
  continuationBytes : Bits8 -> Maybe Nat
  continuationBytes b =
    -- we use binary notation for the magic constants to make
    -- them easily comparable with the values in the table on Wikipedia
    if      (b .&. 0b1000_0000) == 0b0000_0000 then Just 0
    else if (b .&. 0b1110_0000) == 0b1100_0000 then Just 1
    else if (b .&. 0b1111_0000) == 0b1110_0000 then Just 2
    else if (b .&. 0b1111_1000) == 0b1111_0000 then Just 3
    else                                            Nothing

  -- splits a bytestring at the last UTF-8 leading byte.
  splitLeading :
       {n : Nat}
    -> (k : Nat)
    -> ByteVect n
    -> {auto 0 p : LTE k n}
    -> Maybe (ByteString,ByteString,Nat)
  splitLeading 0     x = Nothing
  splitLeading (S k) x =
    case continuationBytes (atNat x k) of
      Nothing  => splitLeading k x
      (Just y) => Just (BS _ $ take k x, BS _ $ drop k x, S y)

  ||| Breaks a list of byte vectors at the last incomplete UTF-8 codepoint
  ||| The first list is a concatenation of all the complete UTF-8 strings,
  ||| while the second list contains the last incomplete codepoint (in case
  ||| of a valid UTF-8 string, the second list holds at most 3 bytes).
  export
  breakAtLastIncomplete : Bytes -> Nat -> SnocBytes -> (Bytes,Bytes)
  breakAtLastIncomplete post n [<]        = ([], post)
  breakAtLastIncomplete post n (pre:<lst@(BS sz bv)) =
    case splitLeading sz bv of
      Nothing => breakAtLastIncomplete (lst :: post) (n + size lst) pre
      Just (prel,postl,trailing) => case trailing <= n + size postl of
        True  => ([fastConcat $ pre <>> (lst::post)], [])
        False => ([fastConcat $ pre <>> [prel]], postl::post)
