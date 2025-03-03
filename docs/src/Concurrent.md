# Concurrent Streams

```idris
module Concurrent

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
counter = mapAccumulate 0 (\n,_ => (S n, n)) $ repeat (sleep 10.ms)

done : Prog es Bool
done = sleep 5.s $> True

prog1 : Prog [Errno] ()
prog1 = (counter `interruptWhen` done) |> take 1000000 |> printLnTo Stdout

prog2 : Prog [Errno] ()
prog2 = ignore (takeWhile (not . null) (repeat ask)) <+> stdoutLn "Time's up! Goodbye!"
  where
    ask : Prog [Errno] ByteString
    ask = do
      stdoutLn "Please enter your name:"
      take 1 $ timeout 5.s (lines $ bytes Stdin 0xff) <+> pure empty

covering
main : IO ()
main = runProg prog2
```

<!-- vi: filetype=idris2:syntax=markdown
-->
