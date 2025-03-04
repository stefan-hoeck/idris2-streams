# Concurrent Streams

```idris
module Concurrent

import Data.String

import IO.Async.Loop.Posix
import FS.Stream as S
import FS.Posix
import FS.System

%default total

0 Prog : List Type -> Type -> Type
Prog = AsyncStream Poll

covering
runProg : Prog [Errno] () -> IO ()
runProg prog =
  simpleApp $ run (handle [eval . stderrLn . interpolate] prog)
```

```idris
counter : Prog es Nat
counter = count $ repeat (delayed 10.ms ())

done : Prog es Bool
done = delayed 5.s True

prog1 : Prog [Errno] ()
prog1 = (counter `interruptWhen` done) |> take 1000000 |> printLnTo Stdout

prog2 : Prog [Errno] ()
prog2 = ignore (takeWhile (not . null) (repeat ask)) <+> stdoutLn "Time's up! Goodbye!"
  where
    ask : Prog [Errno] ByteString
    ask = do
      stdoutLn "Please enter your name:"
      take 1 $ timeout 5.s (lines $ bytes Stdin 0xff) <+> pure empty

record Tick where
  constructor T
  ix      : Nat
  counter : Nat

pretty: (Tick, Nat) -> String
pretty (T ix c, tot) =
  "Stream: \{show ix}; Count: \{padLeft 3 ' ' $ show c}; Total: \{padLeft 3 ' ' $ show tot}"

tick : Nat -> Clock Duration -> Prog [Errno] Tick
tick ix dur = T ix <$> count (repeat $ delayed dur ())

prog3 : Prog [Errno] ()
prog3 =
     merge [ tick 1 100.ms, tick 2 700.ms, tick 3 1500.ms, tick 4 300.ms ]
  |> zipWithIndex
  |> map pretty
  |> take 1000
  |> timeout 10.s
  |> linesTo Stdout

covering
main : IO ()
main = runProg prog3
```

<!-- vi: filetype=idris2:syntax=markdown
-->
