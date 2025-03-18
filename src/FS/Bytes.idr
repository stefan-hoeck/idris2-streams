||| Utilities for working with streams of byte arrays.
module FS.Bytes

import public Data.ByteString

import FS.Internal.Bytes
import FS.Pull
import FS.Stream

%default total

-- export
-- breakAtByte :
--      (Bits8 -> Bool)
--   -> Pull f ByteString es o
--   -> Pull f q es (ByteString, Pull f ByteString es o)
-- breakAtByte pred p =
--   assert_total $ uncons p >>= \case
--     Left x           => pure (ByteString.empty, pure x)
--     Right (bss, rem) => ?foo_1

-- ||| Appends a newline character (`0x0a`) to every bytestring
-- ||| emitted by the stream.
-- |||
-- ||| A chunk (list) of bytestring is thus concatenated to a single
-- ||| byte vector. See also `lines`.
-- export
-- unlines : Stream f es ByteString -> ByteStream f es
-- unlines = mapChunk (\cs => fastConcat $ cs >>= \b => [b,nl])
--
-- ||| Breaks the bytes emitted by a byte stream along unix newline
-- ||| characters (`0x0a`).
-- |||
-- ||| For reasons of efficiency, this emits the produce lines as
-- ||| a list of bytestrings.
-- export
-- lines : ByteStream f es -> Stream f es ByteString
-- lines = scanChunkFull empty splitNL last
--   where
--     last : ByteString -> Bytes
--     last (BS 0 _) = []
--     last bs       = [bs]
--
-- namespace UTF8
--   ||| Converts the byte vectors emitted by a stream to byte vectors
--   ||| that always end at whole code points.
--   |||
--   ||| Note: Typically, this needs to be prefixed with the outer namespace:
--   |||       `UTF8.chunks`
--   export
--   chunks : ByteStream f es -> ByteStream f es
--   chunks = scanChunkFull empty UTF8.breakAtLastIncomplete id
--
--   ||| Cuts the byte vectors emitted by a stream at the end of whole
--   ||| UTF-8 code points and converts them to `String`s.
--   |||
--   ||| Note: Typically, this needs to be prefixed with the outer namespace:
--   |||       `UTF8.decode`
--   export %inline
--   decode : ByteStream f es -> CharStream f es
--   decode = map toString . UTF8.chunks
--
--   ||| Converts a stream of strings to UTF-8-encoded byte strings.
--   |||
--   ||| Note: Typically, this needs to be prefixed with the outer namespace:
--   |||       `UTF8.encode`
--   export %inline
--   encode : CharStream f es -> ByteStream f es
--   encode = map fromString
