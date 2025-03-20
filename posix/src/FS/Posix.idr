module FS.Posix

import Data.String
import Data.FilePath
import Derive.Prelude
import FS.Internal.Bytes
import FS.Posix.Internal
import FS.Pull

import public IO.Async.Posix
import public FS.Concurrent
import public FS.Bytes
import public FS.Pull

import public System.Posix.Dir
import public System.Posix.File.Stats
import public System.Posix.File.Type
import public System.Posix.File

%default total
%language ElabReflection

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
  entries_ withParent dir = unfoldEvalMaybe next
    where
      next : Async e es (Maybe String)
      next =
        assert_total $ catch Errno (readdir String dir) >>= \case
          Left x    => if x == ENOENT then next else throw x
          Right res => case res of
            Res ".." => if withParent then pure (Just "..") else next
            Res res  => pure (Just res)
            _        => pure Nothing

  ||| Produces a stream of directory entries.
  |||
  ||| This will not include the parent directory `".."` in the output.
  export
  entries : (pth : Path p) -> AsyncStream e es (Entry p)
  entries pth =
    resource (opendir "\{pth}") $ evalMapMaybe toEntry . entries_ False

    where
      toEntry : String -> Async e es (Maybe $ Entry p)
      toEntry s =
        case (pth />) <$> Body.parse s of
          Nothing     => pure Nothing
          Just newpth => ifError ENOENT Nothing $ do
            stats <- elift1 $ lstat "\{newpth}"
            pure $ Just (E newpth (fromMode stats.mode) stats)

  ||| Like entries but also enters child directories.
  export
  deepEntries : (pth : Path p) -> AsyncStream e es (Entry p)
  deepEntries pth =
    assert_total $ flatMapC (entries pth) $ \e =>
      case e.type of
        Directory => emit e >> deepEntries e.path
        _         => emit e

--------------------------------------------------------------------------------
-- Files
--------------------------------------------------------------------------------

toList : ByteString -> List ByteString
toList (BS 0 _) = []
toList bs       = [bs]

parameters {0    es  : List Type}
           {auto pol : PollH e}
           {auto has : Has Errno es}


  ||| Streams chunks of byte of at most the given size from the given
  ||| file descriptor.
  |||
  ||| This uses non-blocking I/O, so it can also be used for reading from pipes
  ||| such as standard input.
  export %inline
  bytes : FileDesc a => a -> Bits32 -> AsyncStream e es ByteString
  bytes fd buf = unfoldEvalMaybe $ nonEmpty <$> readnb fd _ buf

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
  writeTo : ToBuf r => FileDesc a => a -> AsyncStream e es r -> AsyncStream e es Void
  writeTo fd = foreach (fwritenb fd)

  export
  printLnTo : Show r => FileDesc a => a -> AsyncStream e es r -> AsyncStream e es Void
  printLnTo fd = foreach (fwritenb fd . (++"\n") . show)

  export
  printLnsTo : Show r => FileDesc a => a -> AsyncStream e es (List r) -> AsyncStream e es Void
  printLnsTo fd =
    foreach $ \xs => let impl := ShowToBytes {a = r} in writeLines fd xs

  export
  printTo : Show r => FileDesc a => a -> AsyncStream e es r -> AsyncStream e es Void
  printTo fd = foreach (fwritenb fd . show)

  export
  writeFile : ToBuf r => String -> AsyncStream e es r -> AsyncStream e es Void
  writeFile path str =
    resource (openFile path create 0o666) $ \fd => writeTo fd str

  export
  appendFile : ToBuf r => String -> AsyncStream e es r -> AsyncStream e es Void
  appendFile path str =
    resource (openFile path append 0o666) $ \fd => writeTo fd str
