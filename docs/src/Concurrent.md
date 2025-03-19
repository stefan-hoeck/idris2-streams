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

-- 0 Prog : List Type -> Type -> Type
-- Prog = AsyncStream Poll
--
-- covering
-- runProg : Prog [Errno] () -> IO ()
-- runProg prog =
--   epollApp $ run (handle [eval . stderrLn . interpolate] prog)
```

```idris
-- counter : Prog es Nat
-- counter = runningCount $ repeat (delayed 10.ms ())
--
-- done : Prog es Bool
-- done = delayed 5.s True
--
-- prog1 : Prog [Errno] ()
-- prog1 = (counter `interruptWhen` done) |> take 1000000 |> printLnTo Stdout
--
-- prog2 : Prog [Errno] ()
-- prog2 = ignore (takeWhile (not . null) (repeat ask)) <+> stdoutLn "Time's up! Goodbye!"
--   where
--     ask : Prog [Errno] ByteString
--     ask = do
--       stdoutLn "Please enter your name:"
--       take 1 $ timeout 5.s (lines $ bytes Stdin 0xff) <+> pure empty
--
-- pretty: ((Nat,Nat), Nat) -> String
-- pretty ((ix,c),tot) =
--   "Stream: \{show ix}; Count: \{padLeft 3 ' ' $ show c}; Total: \{padLeft 3 ' ' $ show tot}"
--
-- tick : Nat -> Clock Duration -> Prog [Errno] (Nat,Nat)
-- tick ix dur = zipWithIndex (repeat $ delayed dur ix)
--
-- prog3 : Prog [Errno] ()
-- prog3 =
--      merge [ tick 1 100.ms, tick 2 700.ms, tick 3 1500.ms, tick 4 300.ms ]
--   |> zipWithIndex
--   |> map pretty
--   |> take 1000
--   |> timeout 10.s
--   |> linesTo Stdout
--
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
--
-- handler : HSum [Errno] -> AsyncStream e [Errno] (Either Errno a)
-- handler (Here x) = pure (Left x)
--
-- logRes : Either Errno ByteString -> Async Poll [Errno] ()
-- logRes (Left x)  = stderrLn "Error: \{x}"
-- logRes (Right x) = fwritenb Stdout (x <+> "\n")
--
-- isStop : ByteString -> Bool
-- isStop bs = trim bs == ":q"
--
-- addr : Bits16 -> IP4Addr
-- addr = IP4 [127,0,0,1]
--
-- serve : Socket AF_INET -> Prog [Errno] ()
-- serve cli =
--   finally (close' cli) $
--        bytes cli 0xff
--     |> lines
--     |> takeWhile (not . isStop)
--     |> linesTo cli
--
-- echo : Bits16 -> (n : Nat) -> (0 p : IsSucc n) => Prog [Errno] ()
-- echo port n = parJoin n (serve <$> acceptOn AF_INET SOCK_STREAM (addr port))
--
-- connectTo :
--      (d : Domain)
--   -> SockType
--   -> Addr d
--   -> Async Poll [Errno] (Socket d)
-- connectTo d t addr = do
--   sock <- socketnb d t
--   connectnb sock addr
--   pure sock
--
-- cli : Bits16 -> Prog [Errno] (Either Errno ByteString)
-- cli port =
--   handleErrors handler $
--     bracket
--       (connectTo AF_INET SOCK_STREAM $ addr port)
--       (\cl => close' cl) $ \cl =>
--            (eval $ fwritenb cl "hello from \{show $ fileDesc cl}\n:q\n")
--         |> (>> bytes cl 0xff)
--         |> lines
--         |> map Right
--
-- echoCli : Bits16 -> (n, tot : Nat) -> (0 p : IsSucc n) => Prog [Errno] ()
-- echoCli port n tot = parJoin n (replicate tot $ cli port) |> foreach logRes
--
-- nats : Stream f es Nat
-- nats = iterate 0 S
--
-- range : Nat -> Stream f es Nat
-- range n = take n nats
--
-- emitted : List (Nat,Nat) -> Async Poll es ()
-- emitted (h::t) = putStrLn "emitting \{show h}"
-- emitted _      = putStrLn "empty chunk"
--
-- countChunks : Stream f es a -> Stream f es Nat
-- countChunks = foldChunks 0 (const . S)
--
-- test : (n, par : Nat) -> (0 p : IsSucc par) => Prog [Errno] ()
-- test n (S par) = merge (innerRange <$> [0..par]) |> countChunks |> printLnTo Stdout
--   where
--     innerRange : Nat -> Prog es (Nat,Nat)
--     innerRange x = (,x) <$> range n
--
-- testPar : (n, streams, par : Nat) -> (0 p : IsSucc par) => Prog [Errno] ()
-- testPar n streams par = parJoin par (innerRange <$> range streams) |> countChunks |> printLnTo Stdout
--   where
--     innerRange : Nat -> Prog es (Nat,Nat)
--     innerRange x = (,x) <$> range n
--
-- prog : List String -> Prog [Errno] ()
-- prog ["server", port, n] =
--   case cast {to = Nat} n of
--     S k => echo (cast port) (S k)
--     0   => echo (cast port) 128
-- prog ["client", port, par, tot] =
--   case cast {to = Nat} par of
--     S k => echoCli (cast port) (S k) (cast tot)
--     0   => echoCli (cast port) 128 (cast tot)
-- prog ["test", n, par] =
--   case cast {to = Nat} par of
--     S k => test (cast n) (S k)
--     0   => test (cast n) 128
-- prog ["testpar", n, streams, par] =
--   case cast {to = Nat} par of
--     S k => testPar (cast n) (cast streams) (S k)
--     0   => testPar (cast n) (cast streams) 128
-- prog _ = test 10 1
--
-- covering
-- main : IO ()
-- main = do
--   _ :: t <- getArgs | [] => runProg (prog [])
--   runProg (prog t)
--
```

<!-- vi: filetype=idris2:syntax=markdown
-->
