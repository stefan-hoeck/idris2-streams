module FS.Posix

import Data.String
import FS.Pull
import public FS.Bytes
import public FS.Stream
import public System.Posix.File

%default total

parameters {0    es  : List Type}
           {auto eli : ELift1 World f}
           {auto has : Has Errno es}

  bytesPull : FileDesc a => a -> Bits32 -> Pull f ByteString es ()
  bytesPull fd buf =
    assert_total $ readres fd ByteString buf >>= \case
      Res res     => output1 res >> bytesPull fd buf
      Interrupted => bytesPull fd buf
      NoData      => bytesPull fd buf
      Closed      => pure ()
      EOI         => pure ()

  export %inline
  bytes : FileDesc a => a -> Bits32 -> Stream f es ByteString
  bytes fd buf = S (bytesPull fd buf)

  export %inline
  readBytes : String -> Stream f es ByteString
  readBytes path =
    resource (openFile path O_RDONLY 0) $ \fd => bytes fd 0xffff

  export
  writeTo : ToBuf r => FileDesc a => a -> Stream f es r -> Stream f es ()
  writeTo fd = (>>= eval . fwrite fd)

  export
  writeFile : ToBuf r => String -> Stream f es r -> Stream f es ()
  writeFile path str =
    resource (openFile path create 0o666) $ \fd => writeTo fd str

  export
  appendFile : ToBuf r => String -> Stream f es r -> Stream f es ()
  appendFile path str =
    resource (openFile path append 0o666) $ \fd => writeTo fd str
