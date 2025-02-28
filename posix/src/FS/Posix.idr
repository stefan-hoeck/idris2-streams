module FS.Posix

import Data.String
import FS.Posix.Internal
import FS.Pull

import public FS.Bytes
import public FS.Stream
import public System.Posix.File

%default total

public export
0 ToBytes : Type -> Type
ToBytes a = Cast a ByteString

export %inline
[ShowToBytes] Show a => Cast a ByteString where
  cast = fromString . show

parameters {0    es  : List Type}
           {auto eli : ELift1 World f}
           {auto has : Has Errno es}

  bytesPull : FileDesc a => a -> Bits32 -> Pull World f ByteString es ()
  bytesPull fd buf =
    assert_total $ readres fd ByteString buf >>= \case
      Res res     => output1 res >> bytesPull fd buf
      Interrupted => bytesPull fd buf
      NoData      => bytesPull fd buf
      Closed      => pure ()
      EOI         => pure ()

  export %inline
  bytes : FileDesc a => a -> Bits32 -> Stream World f es ByteString
  bytes fd buf = S (bytesPull fd buf)

  export %inline
  readBytes : String -> Stream World f es ByteString
  readBytes path =
    resource (openFile path O_RDONLY 0) $ \fd => bytes fd 0xffff

  export
  linesTo : ToBytes r => FileDesc a => a -> Stream World f es r -> Stream World f es ()
  linesTo fd = mapChunksEval (writeLines fd)

  export
  printLnTo : Show r => FileDesc a => a -> Stream World f es r -> Stream World f es ()
  printLnTo = linesTo @{ShowToBytes}

  export
  writeTo : ToBytes r => FileDesc a => a -> Stream World f es r -> Stream World f es ()
  writeTo fd = mapChunksEval (writeAll fd)

  export
  writeFile : ToBytes r => String -> Stream World f es r -> Stream World f es ()
  writeFile path str =
    resource (openFile path create 0o666) $ \fd => writeTo fd str

  export
  appendFile : ToBytes r => String -> Stream World f es r -> Stream World f es ()
  appendFile path str =
    resource (openFile path append 0o666) $ \fd => writeTo fd str
