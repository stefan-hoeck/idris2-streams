||| Utilities for working with streams of byte arrays.
module FS.Bytes

import public Data.ByteString

import FS.Internal.Bytes
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
