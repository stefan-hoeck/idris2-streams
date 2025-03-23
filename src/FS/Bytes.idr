||| Utilities for working with streams of byte arrays.
module FS.Bytes

import public Data.ByteString

import Data.Buffer.Mutable
import FS.Internal.Bytes
import FS.Chunk
import FS.Pull

%default total

||| Appends a newline character (`0x0a`) to every bytestring
||| emitted by the stream.
|||
||| A chunk (list) of bytestring is thus concatenated to a single
||| byte vector. See also `lines`.
export
unlines : Pull f (List ByteString) es r -> Pull f ByteString es r
unlines = mapOutput (\cs => fastConcat $ cs >>= \b => [b,nl])

||| Breaks the bytes emitted by a byte stream along unix newline
||| characters (`0x0a`).
|||
||| For reasons of efficiency, this emits the produce lines as
||| a list of bytestrings.
export
lines : Stream f es ByteString -> Stream f es (List ByteString)
lines = scanFull empty splitNL (map pure . nonEmpty)

namespace UTF8
  ||| Converts the byte vectors emitted by a stream to byte vectors
  ||| that always end at whole code points.
  |||
  ||| Note: Typically, this needs to be prefixed with the outer namespace:
  |||       `UTF8.chunks`
  export
  chunks : Stream f es ByteString -> Stream f es ByteString
  chunks = scanFull empty UTF8.breakAtLastIncomplete nonEmpty

  ||| Cuts the byte vectors emitted by a stream at the end of whole
  ||| UTF-8 code points and converts them to `String`s.
  |||
  ||| Note: Typically, this needs to be prefixed with the outer namespace:
  |||       `UTF8.decode`
  export %inline
  decode : Stream f es ByteString -> Stream f es String
  decode = mapOutput toString . UTF8.chunks

  ||| Converts a stream of strings to UTF-8-encoded byte strings.
  |||
  ||| Note: Typically, this needs to be prefixed with the outer namespace:
  |||       `UTF8.encode`
  export %inline
  encode : Stream f es String -> Stream f es ByteString
  encode = mapOutput fromString

--------------------------------------------------------------------------------
-- Chunk Implementation
--------------------------------------------------------------------------------

nebs : ByteString -> Maybe ByteString
nebs (BS 0 _) = Nothing
nebs bs       = Just bs

breakImpl : BreakInstruction -> (Bits8 -> Bool) -> ByteString -> BreakRes ByteString
breakImpl x f bs =
  case break f bs of
    (pre, BS 0 _)      => Keep pre
    (pre, pst@(BS (S k) bv)) => case x of
      PostHit => Broken (nebs pre) (Just pst)
      DropHit => Broken (nebs pre) (nebs $ BS k (tail bv))
      TakeHit =>
        let len := S pre.size
         in Broken (Just $ take len bs) (nebs $ drop len bs)

splitImpl : Nat -> ByteString -> SplitRes ByteString
splitImpl k bs =
  case splitAt k bs of
    Nothing         => All (size bs)
    Just (pre,post) =>
      let Just x := nebs pre  | Nothing => Naught
          Just y := nebs post | Nothing => All (size x)
       in Middle x y

unfoldImpl :
     {n : _}
  -> (st -> Either r (Bits8,st))
  -> st
  -> MBuffer s n
  -> (k : Nat)
  -> {auto ix : Ix k n}
  -> F1 s (UnfoldRes r st ByteString)
unfoldImpl f cur buf 0 t =
  let ibuf # t := unsafeFreeze buf t
   in More (fromIBuffer ibuf) cur # t
unfoldImpl f cur buf (S k) t =
  case f cur of
    Right (v,nxt) =>
      let _ # t := setIx buf k v t
       in unfoldImpl f nxt buf k t
    Left  x =>
      let ibuf # t := unsafeFreezeLTE buf (ixToNat ix) @{ixLTE ix} t
       in case nebs (fromIBuffer ibuf) of
            Nothing => Done x # t
            Just bs => Last x bs # t

export
Chunk ByteString Bits8 where
  filterChunk pred = nebs . filter pred

  breakChunk = breakImpl

  splitChunkAt = splitImpl

  unconsChunk (BS (S k) bv) = Just (at bv 0, nebs (BS k $ tail bv))
  unconsChunk _             = Nothing

  isEmpty (BS 0 _) = True
  isEmpty _        = False

  replicateChunk @{CS n} v = replicate n v

  unfoldChunk @{CS n} f ini = alloc n (\buf => unfoldImpl f ini buf n)
