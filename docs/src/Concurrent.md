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

end : Prog es Bool
end = sleep 5.s $> True

prog1 : Prog [Errno] ()
prog1 = (counter `interruptWhen` end) |> take 1000000 |> printLnTo Stdout

covering
main : IO ()
main = runProg prog1
```

<!-- vi: filetype=idris2:syntax=markdown
-->
