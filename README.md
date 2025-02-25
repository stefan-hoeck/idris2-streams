# Functional, Effectful Streams with Resource Management and Error Handling

This is a library for defining and manipulating streams of data in a clear, concise,
safe, and performant way. In this tutorial, we are going to look in detail
at the capabilities provided by this library. This is a literate Idris2 file,
so we start with some imports and some utilities:

```idris
module README

import FS.Elin as E
import FS.Stream as S
import FS.Posix
import FS.System

%default total

0 Prog : Type -> Type
Prog = Stream (Elin World) [Errno]

runProg : Prog () -> IO ()
runProg prog = runIO (handle [eval . stderrLn . interpolate] prog)
```

## Streams of Data

A `FS.Stream.Stream f es o` can be thought of as a possibly infinite
sequence of values of type `o`, the evaluation and generation of which
happens in effect type `f`, and that might fail with one of the
errors in `es` (a list of types). The API provided by `FS.Stream` is
in many ways similar as the one provided for `List`s: Streams can
be mapped and filtered, their values can be accumulated, and they form
a monad, so that we can get streams of streams, which - just like with
`List`s - will concatenate and emit all values of the inner streams
in sequence. Here's a very simple example:

```idris
example : Stream f es Nat
example = iterate Z S |> takeWhile (< 10_000_000) |> sum
```

Let's break this down: `iterate Z S` generates an infinite stream of
values by repeatedly applying the second argument to the first. In this case,
it generates the sequence of natural numbers. Function `takeWhile`
emits values from a stream until the given predicate returns `False`.
Finally, `sum` accumulates all emitted values in the obvious way.
The operator we use (`|>`) is just reverse function composition from
the Prelude.

There are many ways we can run and test an example, but probably the
canonical one is to run it through an effectful sink, for instance, by
logging the generated values to `stdout`:

```idris
runExample : IO ()
runExample = runProg (example |> printLnTo Stdout)
```

If you run the above (for instance, at the REPL by invoking `:exec runExample`),
you will notice that it prints its result almost immediately, without
consuming a lot of memory. And while a pure recursive function might compute
the result much quicker, doing the same thing with a list that first
has to be generated will be considerably slower, especially when we start
increasing the limit in the predicate.

For instance, on my system this simple test function takes 1.5 seconds when
the limit is increased to `100_000_000`, while doing the same with a simple
list takes more than ten seconds and consumes about 2 GB of memory. It even
completes with the limit set to one billion, while the corresponding
list function runs out of memory (which is to be expected).

```idris
-- Opens every file listed as a command-line arguments,
-- streaming its content and cutting it into a stream
-- of lines. Every line is annotated with its index in the
-- stream and the longest line is printed together with its
-- index.
--
-- Resources are managed automatically: Every file is closed
-- as soon as it has been exhausted, so this can be used to
-- stream thousands of files.
example2 : Stream (Elin World) [Errno] ()
example2 =
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
main = runProg example2
```
<!-- vi: filetype=idris2:syntax=markdown
-->
