# Concurrent Streams

```idris
module Concurrent

import Debug.Trace
import Data.FilePath
import Data.String
import Data.Vect

import FS
import FS.Posix
import FS.Posix.Internal
import FS.Socket
import FS.System
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix

import System

%default total

0 Prog : List Type -> Type -> Type
Prog = AsyncStream Poll

covering
runProg : Prog [Errno] () -> IO ()
runProg prog =
  epollApp $ run (handle [eval . stderrLn . interpolate] prog)
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

handler : HSum [Errno] -> AsyncStream e [Errno] (Either Errno a)
handler (Here x) = pure (Left x)

logRes : Either Errno ByteString -> Async Poll [Errno] ()
logRes (Left x)  = stderrLn "Error: \{x}"
logRes (Right x) = fwritenb Stdout (x <+> "\n")

serve : Socket AF_INET -> Prog [Errno] (Either Errno ByteString)
serve cli = do
  handleErrors handler $
    bracket
      (pure cli)
      (\_ => sleep 100.ms >> close' cli) $ \_ =>
           bytes cli 0xffff
        |> lines
        |> takeWhile (not . isStop)
        |> observeChunk (\b => sleep 1.s >> ignore (writeLines cli b))
        |> map Right

connectTo :
     (d : Domain)
  -> SockType
  -> Addr d
  -> Async Poll [Errno] (Socket d)
connectTo d t addr = do
  sock <- socketnb d t
  connectnb sock addr
  pure sock

addr : IP4Addr
addr = IP4 [127,0,0,1] 5555

cli : Prog [Errno] (Either Errno ByteString)
cli =
  handleErrors handler $
    bracket
      (connectTo AF_INET SOCK_STREAM addr)
      (\cl => sleep 100.ms >> close' cl) $ \cl =>
           (eval $ sleep 1.s >> fwritenb cl "hello from \{show $ fileDesc cl}\n:q\n")
        |> (>> bytes cl 0xffff)
        |> lines
        |> map Right

echo : (n : Nat) -> (0 p : IsSucc n) => Prog [Errno] ()
echo n =
     parJoin n (serve <$> acceptOn AF_INET SOCK_STREAM addr)
  |> foreach logRes

echoCli : (n : Nat) -> (0 p : IsSucc n) => Prog [Errno] ()
echoCli n = parJoin n (replicate n cli) |> foreach logRes

nats : Stream f es Nat
nats = iterate 0 S

range : Nat -> Stream f es Nat
range n = take n nats

test : (n, par : Nat) -> (0 p : IsSucc par) => Prog [Errno] ()
test n par = parJoin par (innerRange <$> range n) |> printLnTo Stdout
  where
    innerRange : Nat -> Stream f es (Nat,Nat)
    innerRange n = (,n) <$> range n

prog : List String -> Prog [Errno] ()
prog ["server", n] =
  case cast {to = Nat} n of
    S k => echo (S k)
    0   => echo 128
prog ["client", n] =
  case cast {to = Nat} n of
    S k => echoCli (S k)
    0   => echoCli 128
prog ["test", n, par] =
  case cast {to = Nat} par of
    S k => test (cast n) (S k)
    0   => test (cast n) 128
prog _ = test 10 1

covering
main : IO ()
main = do
  _ :: t <- getArgs | [] => runProg (prog [])
  runProg (prog t)

```

<!-- vi: filetype=idris2:syntax=markdown
-->
