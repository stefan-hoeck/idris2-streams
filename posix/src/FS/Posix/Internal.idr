module FS.Posix.Internal

import FS.Internal.Bytes
import System.Posix.File

%default total

parameters {auto fid : FileDesc a}
           (fd       : a)
           {auto has : Has Errno es}
           {auto eoi : EIO1 f}

  bytes : SnocList ByteString -> f es ()
  bytes [<]   = pure ()
  bytes [<bs] = fwrite fd bs
  bytes bss   = fwrite fd (fastConcat $ bss <>> [])

  ||| Writes a chunk of data
  export
  writeAll : Cast r ByteString => List r -> f es (List ())
  writeAll = ($> []) . go [<]
    where
      go : SnocList ByteString -> List r -> f es ()
      go sx []        = bytes sx
      go sx (x :: xs) =
        case cast {to = ByteString} x of
          BS 0 _ => go sx xs
          bs     => go (sx :< bs) xs

  ||| Writes a chunk of data, inserting a newline character (`0x0a`)
  ||| after every item.
  export
  writeLines : Cast r ByteString => List r -> f es (List ())
  writeLines = ($> []) . go [<]
    where
      go : SnocList ByteString -> List r -> f es ()
      go sx []        = bytes sx
      go sx (x :: xs) =
        case cast {to = ByteString} x of
          BS 0 _ => go (sx :< nl) xs
          bs     => go (sx :< bs :< nl) xs
