# Effectful, Concurrent Streams

This is a library for defining and manipulating streams of data in a clear, concise,
safe, and performant way. In this tutorial, we are going to look in detail
at the capabilities provided by this library. This is a literate Idris2 file,
so we start with some imports and some utilities:

```idris
module README

import Data.Bits
import Derive.Prelude
import FS.Elin as E
import FS.Posix
import IO.Async.Loop.Posix
import System

%default total
%language ElabReflection
```

## The Pull Data Type

The core data type provided by this library is an `FS.Core.Pull f o es r`.
The `f` is the effect type the pull will be evaluated in. This is typically
an I/O type such as `Async e`, but it is also possible to evaluate
streams of data in a pure setting using the `Elin s` monad. In this first
part, we are going to explain the key concepts with `Elin`. Parameter `o`
is the *output type*: A pull produces an arbitrary amount of output of
this type before it either fails with an error of type `HSum es` or
succeeds with a result of type `r`. In order to demonstrate all of
this, we are going to setup a couple of utilities:

```idris
0 Pure : (s,o,r : Type) -> Type
Pure s o r = Pull (Elin s) o [String] r

public export
record Res o r where
  constructor R
  outcome : Outcome [String] r
  output  : List o

%runElab derive "Res" [Show,Eq]

export covering
runPure : Show o => Show r => (forall s . Pure s o r) -> IO ()
runPure p =
  printLn $ either absurd id $ runElin $ do
    ref <- newref [<]
    out <- pull $ foreach (\x => mod ref (:< x)) p
    sv  <- readref ref
    pure (R out $ sv <>> [])
```

The above runs a pull in the `Elin s` monad, setting up a mutable reference
where all generated output will be written to. The accumulated output and
final result is wrapped up in a utility record type.

With this, we are ready to run a couple of experiments at the REPL. For
instance, a `Pull` is a monad with regard to its result type, so we
can do typical monad stuff:

```idris
pureExample : Pure s () Nat
pureExample = pure 12

mapped : Pure s () String
mapped = map show pureExample

app : Pure s () Nat
app = [| pureExample + pureExample |]
```

And at the REPL:

```sh
README> :exec runPure pureExample
R {outcome = Succeeded 12, output = []}
README> :exec runPure mapped
R {outcome = Succeeded "12", output = []}
README> :exec runPure app
R {outcome = Succeeded 24, output = []}
```

A much more interesting and important aspect is the capability of
a `Pull` to emit values before it terminates with a result:

```idris
singleVal : Pure s Nat ()
singleVal = emit 10

manyVals : Pure s Nat ()
manyVals = emits [0..9]
```

And at the REPL:

```sh
README> :exec runPure singleVal
R {outcome = Succeeded (), output = [10]}
README> :exec runPure manyVals
R {outcome = Succeeded (), output = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]}
README> :exec runPure (manyVals >> singleVal)
R {outcome = Succeeded (), output = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]}
```

The last example shows that when we sequence pulls, all output they
generate will be emitted in sequence as well.

Finally, a pull provides the capability to fail with and handle errors.
Here's an example:

```idris
failAt5 : Nat -> Pure s Nat ()
failAt5 0     = pure ()
failAt5 5     = throw "5 is invalid!"
failAt5 (S k) = emit k >> failAt5 k
```

The following REPL session shows, that the generated pull produces
output until the magic number `5` is encountered, at which point it
immediately fails with an error.

```sh
README> :exec runPure (failAt5 4)
R {outcome = Succeeded (), output = [3, 2, 1, 0]}
README> :exec runPure (failAt5 10)
R {outcome = Error (Here "5 is invalid!"), output = [9, 8, 7, 6, 5]}
```

A pull can be thought of as a possibly infinite sequence of values
just like a pure Idris `Prelude.Stream.Stream`. As such, we can perform
typical stream operations on it: Mapping, filtering, and accumulating
values. Here's an example (`|>` is the reverse function composition operator
from the Prelude. It is very convenient for describing sequences of
pull transformations):

```idris
oddNats : Pure s Integer ()
oddNats = iterate 0 S |> P.mapOutput cast |> filter odd |> take 10 |> sum
  where
    odd : Integer -> Bool
    odd n = (n `mod` 2) == 1
```

Here's the corresponding REPL output:

```sh
README> :exec runPure oddNats
R {outcome = Succeeded (), output = [100]}
```

Let's break the above down a bit: `iterate 0 S` generates the infinite
sequence of natural numbers, `mapOutput cast` converts all output to
type `Integer`, `filter odd` keeps only the odd numbers, `take 10`
discards everything but the first ten values, and `sum` adds everything
up and emits a single final result (I'm going to later explain why
`mapOutput` needs to be partially qualified here).

### Effectful Streams

As a next example, we are going to look at effectful streams.
For this, we are going to implement a pseudo-random number generator (PSNG)
(taken from a [Gist by Tommy Ettinger](https://gist.github.com/tommyettinger/46a874533244883189143505d203312c)).

There are - as always - several ways to generate values in a stateful
manner. In our case, we make use of an auto-implicit argument
that is used to store the internal state of the PSNG and allows
us to compute the next value in an effectful way:

```idris
export
record Rnd s where
  constructor MkRnd
  base : Ref s Bits32

makeRnd : Lift1 s f => Bits32 -> f (Rnd s)
makeRnd seed = MkRnd <$> newref seed

setSeed : Lift1 s f => (rnd : Rnd s) => Bits32 -> f ()
setSeed = writeref rnd.base

next1 : Rnd s => F1 s Bits32
next1 @{rnd} t =
  let b0 # t := read1 rnd.base t
      z      := b0 + 0x9e3779b9
      _  # t := write1 rnd.base z t
      z1     := (z `xor` (z `shiftR` 16)) * 0x21f0aaad
      z2     := (z1 `xor` (z1 `shiftR` 15)) * 0x735a2d97
   in (z2 `xor` (z2 `shiftR` 15)) # t
```

With the above stateful computation at hand, we can easily
create an infinite stream of pseudo-random numbers:

```idris
numbers : Rnd s => Pure s Bits32 ()
numbers = repeat (eval $ lift1 next1)

roll : (n : Nat) -> Bits32 -> Nat
roll n v = 1 + cast (v `mod` cast n)
```

Below is some glue code to run streams requiring an implicit PRNG
with the option to generate a starting seed from system entropy
or providing one manually.

```idris
%foreign "scheme:blodwen-random"
         "javascript:lambda:x=>Math.floor(Math.random() * Number(x))"
prim__random_Bits32 : Bits32 -> PrimIO Bits32

randomSeed : IO Bits32
randomSeed = primIO $ prim__random_Bits32 0xffff_ffff

export covering
runRnd :
     {default Nothing seed : Maybe Bits32}
  -> {auto sho : Show o}
  -> {auto shr : Show r}
  -> (forall s . Rnd s => Pure s o r)
  -> IO ()
runRnd p = do
  sd <- maybe randomSeed pure seed
  runPure $ do
    rnd <- makeRnd sd
    p @{rnd}
```

Let's roll some dice. We want to count the number of rolls it
takes until we achieve the maximum possible result of a
die roll:

```idris
rollsTillMax : Rnd s => Nat -> Pure s Nat ()
rollsTillMax die =
     numbers
  |> P.mapOutput (roll die)
  |> P.takeThrough (die >)
  |> count
```

And at the REPL:

```sh
README> :exec runRnd (rollsTillMax 10)
R {outcome = Succeeded (), output = [23]}
```

### Chunks and Performance

If you run the last example with a very large die, it will - quite
naturally - take a considerable amount of time to come up with
a result. The following, for instance, takes about half a minute on
my machine:

```sh
README> :exec runRnd {seed = Just 0} (rollsTillMax 100_000_000)
R {outcome = Succeeded (), output = [36341485]}
```

There are many reasons, why this takes a lot of time. It computes
close to forty million random numbers after all, an our PRNG has not
been maximally optimized for performance.

The biggest impact on performance, however, comes from the streaming
machinery itself. Running our streams - as we will see in the next
section - takes care of a lot of book keeping for us, and therefore
comes with a considerable overhead. For processing large amounts
of data (typically, millions of values or megabytes of file input),
we want the data to be processed in larger chunks to reduce the
impact coming from the streaming library.

Here is the die rolling example again, but this time we generate
chunks of values wrapped in lists of the given `ChunkSize`.
The default chunk size is 128 but this can be overridden by
passing a value literally.

```idris
nexts1 : Rnd s => SnocList Bits32 -> Nat -> F1 s (List Bits32)
nexts1 sx 0     t = (sx <>> []) # t
nexts1 sx (S k) t = let x # t := next1 t in nexts1 (sx:<x) k t

numbersLst : ChunkSize => Rnd s => Pure s (List Bits32) ()
numbersLst @{CS n} = repeat (eval $ lift1 $ nexts1 [<] n)

rollsTillMaxLst : ChunkSize => Rnd s => Nat -> Pure s Nat ()
rollsTillMaxLst die =
     numbersLst
  |> C.mapOutput (roll die)
  |> C.takeThrough (die >)
  |> C.count
```

In the code above, we now see why so far we had to prefix many of
our streaming functions with a `P.`: Functions that operate on a
pull's output come in two versions. The ones operating at output
values directly can be found in module `FS.Pull`, which is
imported qualified as `P`. The ones operating on the elements
of larger chunks such as lists, arrays, or byte vectors,
can be found in `FS.Chunk`, which is imported qualified as `C`.

We can now experiment with the impact this has on performance:

```sh
README> :exec runRnd {seed = Just 0} (rollsTillMaxLst @{1024} 100_000_000)
R {outcome = Succeeded (), output = [36341485]}
README> :exec runRnd {seed = Just 0} (rollsTillMaxLst @{10} 100_000_000)
R {outcome = Succeeded (), output = [36341485]}
README> :exec runRnd {seed = Just 0} (rollsTillMaxLst @{1} 100_000_000)
R {outcome = Succeeded (), output = [36341485]}
```

## Streaming `IO`

While having a versatile API for working with pure streams of values can be
useful, the real use case for libraries such as this one is to stream data
coming from and going to `IO` sources and sinks: Files, sockets, databases.

Here's a second example, which reads a text file line by line and converts
all numeric entries from degrees Fahrenheit to Celsius.

```idris
0 Prog : Type -> Type
Prog = AsyncStream Poll [Errno]

covering
runProg : Prog Void -> IO ()
runProg prog =
  simpleApp $ mpull (handle [stderrLn . interpolate] prog)

toCelsius : ByteString -> Double
toCelsius bs =
  case parseDouble bs of
    Nothing => 0.0
    Just f  => (f - 32.0) * (5.0/9.0)

fahrenheit : Prog Void
fahrenheit =
     readBytes "resources/fahrenheit.txt"
  |> lines
  |> C.filterNot (\x => null (trim x) || isPrefixOf "//" x)
  |> C.mapOutput (fromString . show . toCelsius)
  |> unlines
  |> writeTo Stdout
```

The above will convert every line in file `resources/fahrenheit.txt`
to Celsius, skipping empty lines and comments. This is already very
convenience, but under the hood, it does so much more:

* It performs error handling: When the file in question is not present
  or can't be read, it will fail with an exception of type `Errno` and
  print it to `stderr`.
* If the file can be opened, it will be properly closed when the
  stream of values has been exhausted.

Here's an example that can potentially open thousands of files (given
as command-line arguments) and emit their content as a stream of
`ByteStrings`, which will then be processed one line at a time.

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
idrisLines : Prog String -> Prog Void
idrisLines args =
     args
  |> observe stdoutLn
  |> bind readBytes
  |> lines
  |> C.mapOutput size
  |> C.zipWithIndex
  |> C.fold max (Z,Z)
  |> printLnTo Stdout

prog : List String -> Prog Void
prog []     = throw EINVAL
prog (_::t) = case t of
  ["fahrenheit"]   => fahrenheit
  "idris-lines"::t => idrisLines (emits t)
  _                => stderrLn "Invalid commandline arguments"

covering
main : IO ()
main = getArgs >>= runProg . prog
```
<!-- vi: filetype=idris2:syntax=markdown
-->
