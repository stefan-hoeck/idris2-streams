# Concurrent Streams

```idris
module Concurrent

import Debug.Trace
import Data.FilePath
import Data.String
import Data.Vect

import IO.Async.Loop.Posix
import FS.Stream as S
import FS.Posix
import FS.Socket
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
counter = runningCount $ repeat (delayed 10.ms ())

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

pretty: ((Nat,Nat), Nat) -> String
pretty ((ix,c),tot) =
  "Stream: \{show ix}; Count: \{padLeft 3 ' ' $ show c}; Total: \{padLeft 3 ' ' $ show tot}"

tick : Nat -> Clock Duration -> Prog [Errno] (Nat,Nat)
tick ix dur = zipWithIndex (repeat $ delayed dur ix)

prog3 : Prog [Errno] ()
prog3 =
     merge [ tick 1 100.ms, tick 2 700.ms, tick 3 1500.ms, tick 4 300.ms ]
  |> zipWithIndex
  |> map pretty
  |> take 1000
  |> timeout 10.s
  |> linesTo Stdout

prettyEntry : Entry Rel -> String
prettyEntry (E path type stats) = "\{path}: \{show type}"

idrisLines : Prog [Errno] ()
idrisLines =
     deepEntries {p = Rel} "."
  |> filter (regularExt "idr")
  |> (>>= content)
  |> lines
  |> count
  |> printLnTo Stdout

isStop : ByteString -> Bool
isStop bs = trim bs == ":q"

echo : Prog [Errno] ()
echo = do
  srv <- acceptOn AF_INET SOCK_STREAM (IP4 [127,0,0,1] 5555)
  stdoutLn ("Got a connection (file descriptor: \{show $ fileDesc srv})")
  handleErrors (\case Here x => stderrLn "\{x}") (serve srv)

  where
    serve : Socket AF_INET -> Prog [Errno] ()
    serve sock =
      resource (pure (Socket.R sock)) $ \_ =>
           bytes sock 0xffff
        |> observe (fwritenb Stdout)
        |> lines
        |> takeWhile (not . isStop)
        |> linesTo sock

covering
main : IO ()
main = runProg echo
```

<!-- vi: filetype=idris2:syntax=markdown
-->
