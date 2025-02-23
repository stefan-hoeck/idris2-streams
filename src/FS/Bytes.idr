||| Utilities for working with streams of byte arrays.
module FS.Bytes

import public Data.ByteString

import FS.Internal.Bytes
import FS.Stream

%default total

||| Appends a newline character (`0x0a`) to every bytestring
||| emitted by the stream.
export
unlines : Stream f es ByteString -> Stream f es ByteString
unlines = mapChunks (>>= \b => [b,nl])

||| Breaks the bytes emitted by a byte stream along unix newline
||| characters (`0x0a`).
export
lines : Stream f es ByteString -> Stream f es ByteString
lines = scanChunksFull [<] (splitNL [<]) last
  where
    last : SnocBytes -> Bytes
    last sx =
      case fastConcat (sx <>> []) of
        BS 0 _ => []
        bs     => [bs]

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
      (\pre,cur => UTF8.breakAtLastIncomplete [] 0 $ [<] <>< (pre ++ cur))
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
