module FS.Posix.Internal

import FS.Internal.Bytes
import IO.Async.Posix

%default total

parameters {auto fid : FileDesc a}
           (fd       : a)
           {auto has : Has Errno es}
           {auto ph  : PollH e}

  bytes : SnocList ByteString -> Async e es ()
  bytes [<]   = pure ()
  bytes [<bs] = fwritenb fd bs
  bytes bss   = fwritenb fd (fastConcat $ bss <>> [])

  ||| Writes a chunk of data
  export
  writeAll : Cast r ByteString => List r -> Async e es ()
  writeAll = go [<]
    where
      go : SnocList ByteString -> List r -> Async e es ()
      go sx []        = bytes sx
      go sx (x :: xs) =
        case cast {to = ByteString} x of
          BS 0 _ => go sx xs
          bs     => go (sx :< bs) xs

  ||| Writes a chunk of data, inserting a newline character (`0x0a`)
  ||| after every item.
  export
  writeLines : Cast r ByteString => List r -> Async e es ()
  writeLines = go [<]
    where
      go : SnocList ByteString -> List r -> Async e es ()
      go sx []        = bytes sx
      go sx (x :: xs) =
        case cast {to = ByteString} x of
          BS 0 _ => go (sx :< nl) xs
          bs     => go (sx :< bs :< nl) xs
