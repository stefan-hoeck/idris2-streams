# idris2-streams: Functional, effectful streams with resource management and error handling

This is still very much work in progress, but here is a teaser
program:

```idris
module README

import Control.Monad.Elin
import FS.Posix
import FS.System

%default total

-- Opens every file listed as a command-line arguments,
-- streaming its content and cutting it into a stream
-- of lines. Every line is annotated with its index in the
-- stream and the longest line is printed together with its
-- index.
--
-- Resources are managed automatically: Every file is closed
-- as soon as it has been exhausted, so this can be used to
-- stream thousands of files.
example : Stream (Elin World) [Errno] ()
example =
     tail args
  |> observe stdoutLn
  |> (>>= readBytes)
  |> lines
  |> map size
  |> zipWithIndex
  |> fold (Z,Z) max
  |> map (fromString . show)
  |> unlines
  |> writeTo Stdout

covering
main : IO ()
main = ignore $ runElinIO $ handle [stderrLn . interpolate] (run example)
```
<!-- vi: filetype=idris2:syntax=markdown
-->
