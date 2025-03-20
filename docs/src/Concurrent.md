# Concurrent Streams

```idris
module Concurrent

import Debug.Trace
import Data.FilePath
import Data.String
import Data.Vect

import FS
import FS.Chunk
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
runProg : Prog [Errno] Void -> IO ()
runProg prog = epollApp $ mpull (handle [stderrLn . interpolate] prog)
```

```idris
counter : Prog es (List Nat)
counter = runningCount $ repeat (delayed 10.ms [()])

prog1 : Prog [Errno] Void
prog1 = timeout 5.s counter |> takeC 1000000 |> printLnTo Stdout

prog2 : Prog [Errno] ByteString
prog2 = takeWhileC (not . null) (repeat ask) <+> stdoutLn "Time's up! Goodbye!"
  where
    ask : Prog [Errno] ByteString
    ask = do
      stdoutLn "Please enter your name:"
      takeC 1 $ timeout 5.s (bytes Stdin 0xff) <+> emit empty

pretty: ((Nat,Nat), Nat) -> String
pretty ((ix,c),tot) =
  "Stream: \{show ix}; Count: \{padLeft 3 ' ' $ show c}; Total: \{padLeft 3 ' ' $ show tot}"

tick : Nat -> Clock Duration -> Prog [Errno] (List (Nat,Nat))
tick ix dur = zipWithIndex (repeat $ delayed dur [ix])

prog3 : Prog [Errno] Void
prog3 =
     merge [ tick 1 100.ms, tick 2 700.ms, tick 3 1500.ms, tick 4 300.ms ]
  |> zipWithIndex
  |> mapEl pretty
  |> take 1000
  |> timeout 10.s
  |> printLnsTo Stdout

-- prettyEntry : Entry Rel -> String
-- prettyEntry (E path type stats) = "\{path}: \{show type}"
--
-- idrisLines : Prog [Errno] ()
-- idrisLines =
--      deepEntries {p = Rel} "."
--   |> filter (regularExt "idr")
--   |> (>>= content)
--   |> lines
--   |> count
--   |> printLnTo Stdout

handler : HSum [Errno] -> AsyncStream e [Errno] (Either Errno a)
handler (Here x) = emit (Left x)

logRes : Either Errno ByteString -> Async Poll [Errno] ()
logRes (Left x)  = stderrLn "Error: \{x}"
logRes (Right x) = fwritenb Stdout x

isStop : ByteString -> Bool
isStop bs = trim bs == ":q"

addr : Bits16 -> IP4Addr
addr = IP4 [127,0,0,1]

serve : Socket AF_INET -> Prog [Errno] Void
serve cli =
  finally (close' cli) $
       bytes cli 0xff
    |> lines
    |> takeWhile (not . isStop)
    |> unlines
    |> writeTo cli

echo : Bits16 -> (n : Nat) -> (0 p : IsSucc n) => Prog [Errno] Void
echo port n = parJoin n (mapC serve $ acceptOn AF_INET SOCK_STREAM (addr port))

connectTo :
     (d : Domain)
  -> SockType
  -> Addr d
  -> Async Poll [Errno] (Socket d)
connectTo d t addr = do
  sock <- socketnb d t
  connectnb sock addr
  pure sock

cli : Bits16 -> Prog [Errno] (Either Errno ByteString)
cli port =
  handleErrors handler $
    Pull.bracket
      (connectTo AF_INET SOCK_STREAM $ addr port)
      (\cl => close' cl) $ \cl =>
           (eval $ fwritenb cl "hello from \{show $ fileDesc cl}\n:q\n")
        |> bindC (\_ => bytes cl 0xff)
        |> mapC Right

echoCli : Bits16 -> (n, tot : Nat) -> (0 p : IsSucc n) => Prog [Errno] Void
echoCli port n tot = parJoin n (replicateC tot $ cli port) |> foreach logRes

nats : Stream f es (List Nat)
nats = iterate 0 S

range : Nat -> Stream f es (List Nat)
range n = take n nats

emitted : List (Nat,Nat) -> Async Poll es ()
emitted (h::t) = putStrLn "emitting \{show h}"
emitted _      = putStrLn "empty chunk"

test : (n, par : Nat) -> (0 p : IsSucc par) => Prog [Errno] Void
test n (S par) = merge (innerRange <$> [0..par]) |> countC |> printLnTo Stdout
  where
    innerRange : Nat -> Prog es (List (Nat,Nat))
    innerRange x = mapEl (,x) (range n)

prog : List String -> Prog [Errno] Void
prog ["server", port, n] =
  case cast {to = Nat} n of
    S k => echo (cast port) (S k)
    0   => echo (cast port) 128
prog ["client", port, par, tot] =
  case cast {to = Nat} par of
    S k => echoCli (cast port) (S k) (cast tot)
    0   => echoCli (cast port) 128 (cast tot)
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
