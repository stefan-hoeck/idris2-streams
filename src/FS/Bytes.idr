||| Utilities for working with streams of byte arrays.
module FS.Bytes

import Data.Bits
import Data.ByteString
import FS.Stream

%default total

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

-- breaks a list of byte vectors at the last incomplete UTF-8 codepoint
-- The first list is a concatenation of all the complete UTF-8 strings,
-- while the second list contains the last incomplete codepoint (in case
-- of a valid UTF-8 string, the second list holds at most 3 bytes).
breakAtLastCodepoint :
     List ByteString
  -> Nat
  -> SnocList ByteString
  -> (List ByteString, List ByteString)
breakAtLastCodepoint post n [<]        = ([], post)
breakAtLastCodepoint post n (pre:<lst@(BS sz bv)) =
  case splitLeading sz bv of
    Nothing => breakAtLastCodepoint (lst :: post) (n + size lst) pre
    Just (prel,postl,trailing) => case trailing <= n + size postl of
      True  => ([fastConcat $ pre <>> (lst::post)], [])
      False => ([fastConcat $ pre <>> []], postl::post)

namespace UTF8
  ||| Converts the byte vectors emitted by a stream to byte vectors
  ||| that always end at whole code points.
  |||
  ||| Note: Typically, this needs to be prefixed with the outer namespace:
  |||       `UTF8.chunks`
  export
  chunks : Stream f es ByteString -> Stream f es ByteString
  chunks =
    scanChunksFull
      []
      (\pre,cur => breakAtLastCodepoint [] 0 $ [<] <>< (pre ++ cur))
      (pure . fastConcat)

  ||| Cuts the byte vectors emitted by a stream at the end of whole
  ||| UTF-8 code points and converts them to `String`s.
  |||
  ||| Note: Typically, this needs to be prefixed with the outer namespace:
  |||       `UTF8.decode`
  export %inline
  decode : Stream f es ByteString -> Stream f es String
  decode = map toString . UTF8.chunks

  ||| Converts a stream of strings to UTF-8-encoded byte strings.
  |||
  ||| Note: Typically, this needs to be prefixed with the outer namespace:
  |||       `UTF8.encode`
  export %inline
  encode : Stream f es String -> Stream f es ByteString
  encode = map fromString
