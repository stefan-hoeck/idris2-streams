module FS.Posix

import Data.String
import Data.FilePath
import Derive.Prelude
import FS.Posix.Internal
import FS.Pull

import public IO.Async.Posix
import public FS.Concurrent
import public FS.Bytes
import public FS.Stream

import public System.Posix.Dir
import public System.Posix.File.Stats
import public System.Posix.File.Type
import public System.Posix.File

%default total
%language ElabReflection

||| Utility for converting a value to a byte vector.
public export
0 ToBytes : Type -> Type
ToBytes a = Cast a ByteString

export %inline
[ShowToBytes] Show a => Cast a ByteString where
  cast = fromString . show

--------------------------------------------------------------------------------
-- Directories
--------------------------------------------------------------------------------

public export
record Entry (p : PathType) where
  constructor E
  path  : Path p
  type  : FileType
  stats : FileStats

%runElab deriveIndexed "Entry" [Show,Eq]

||| True if the given directory entry is hidden.
export %inline
hidden : Entry p -> Bool
hidden = isHidden . path

||| True if the given directory entry is a regular file
export %inline
regular : Entry p -> Bool
regular = (Regular ==) . type

||| True if the given directory entry is a regular file
||| with the given extension.
export %inline
regularExt : Body -> Entry p -> Bool
regularExt b e = regular e && Just b == extension e.path

parameters {0    es  : List Type}
           {auto has : Has Errno es}

  ||| Produces a stream of directory entries.
  |||
  ||| This is a low-level utility to just emit the content of a directory.
  ||| Use `entries` to get proper file paths and information about the types
  ||| and stats of files.
  export
  entries_ : (withParent : Bool) -> Dir -> AsyncStream e es String
  entries_ withParent dir =
    unfoldEvalChunk $ ifError ENOENT (Just []) $ readdir String dir >>= \case
      Res ".." => pure (Just (if withParent then [".."] else []))
      Res res  => pure (Just [res])
      _        => pure Nothing

  ||| Produces a stream of directory entries.
  |||
  ||| This will not include the parent directory `".."` in the output.
  export
  entries : (pth : Path p) -> AsyncStream e es (Entry p)
  entries pth =
    resource (opendir "\{pth}") $ evalMapChunk toEntries . entries_ False

    where
      toEntry : String -> Async e es (List $ Entry p)
      toEntry s =
        case (pth />) <$> Body.parse s of
          Nothing     => pure []
          Just newpth => ifError ENOENT [] $ do
            stats <- elift1 $ lstat "\{newpth}"
            pure [E newpth (fromMode stats.mode) stats]

      toEntries : List String -> Async e es (List $ Entry p)
      toEntries = map join . traverse toEntry

  ||| Like entries but also enters child directories.
  export
  deepEntries : (pth : Path p) -> AsyncStream e es (Entry p)
  deepEntries pth =
    assert_total $ do
      e <- entries pth
      case e.type of
        Directory => cons1 e (deepEntries e.path)
        _         => pure e

--------------------------------------------------------------------------------
-- Files
--------------------------------------------------------------------------------

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

  ||| Streams chunks of byte of at most the given size from the given
  ||| file descriptor.
  |||
  ||| This uses non-blocking I/O, so it can also be used for reading from pipes
  ||| such as standard input.
  export %inline
  bytes : FileDesc a => a -> Bits32 -> AsyncStream e es ByteString
  bytes fd buf = S (bytesPull fd buf)

  ||| Tries to open the given file and starts reading chunks of bytes
  ||| from the created file descriptor.
  export %inline
  readBytes : String -> AsyncStream e es ByteString
  readBytes path =
    resource (openFile path O_RDONLY 0) $ \fd => bytes fd 0xffff

  ||| Streams the content of a directory entry
  export %inline
  content : Entry p -> AsyncStream e es ByteString
  content = readBytes . interpolate . path

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
