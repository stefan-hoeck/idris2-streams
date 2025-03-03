module FS.Posix

import Data.String
import FS.Posix.Internal
import FS.Pull

import public IO.Async.Posix
import public FS.Concurrent
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

toList : ByteString -> List ByteString
toList (BS 0 _) = []
toList bs       = [bs]

parameters {0    es  : List Type}
           {auto pol : PollH e}
           {auto has : Has Errno es}

  bytesPull : FileDesc a => a -> Bits32 -> AsyncPull e ByteString es ()
  bytesPull fd buf =
    assert_total $ Eval (readnb fd _ buf) >>= \case
      BS 0 _ => pure ()
      bs     => output1 bs >> bytesPull fd buf

  export %inline
  bytes : FileDesc a => a -> Bits32 -> AsyncStream e es ByteString
  bytes fd buf = S (bytesPull fd buf)

  export %inline
  readBytes : String -> AsyncStream e es ByteString
  readBytes path =
    resource (openFile path O_RDONLY 0) $ \fd => bytes fd 0xffff

  export
  linesTo : ToBytes r => FileDesc a => a -> AsyncStream e es r -> AsyncStream e es ()
  linesTo fd = mapChunksEval (writeLines fd)

  export
  printLnTo : Show r => FileDesc a => a -> AsyncStream e es r -> AsyncStream e es ()
  printLnTo = linesTo @{ShowToBytes}

  export
  writeTo : ToBytes r => FileDesc a => a -> AsyncStream e es r -> AsyncStream e es ()
  writeTo fd = mapChunksEval (writeAll fd)

  export
  writeFile : ToBytes r => String -> AsyncStream e es r -> AsyncStream e es ()
  writeFile path str =
    resource (openFile path create 0o666) $ \fd => writeTo fd str

  export
  appendFile : ToBytes r => String -> AsyncStream e es r -> AsyncStream e es ()
  appendFile path str =
    resource (openFile path append 0o666) $ \fd => writeTo fd str
