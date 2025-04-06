# Reusing Connections: HTTP 1.1

In the [previous part](HTTP.md), we wrote a basic HTTP 1.0 server that was already
quite performant. We are now going to speed things up by moving to HTTP 1.1,
which will allow us to handle many requests over a single connection.

```idris
module HTTP11

import Data.Vect
import HTTP

%default total
```

## Loop till Nothing

In function `request`, which converts the header of an HTTP message to
a `Request` data type, we already dealt with the possibility of the
message being empty. We can now take this as a sign that the connection
has been closed by the client:

```idris
response : Maybe Request -> HTTPPull ByteString Bool
response Nothing  = pure False
response (Just r) = cons resp r.body $> True
  where
    resp : ByteString
    resp = case r.type of
      Nothing => ok [("Content-Length",show r.length)]
      Just t  => ok [("Content-Type",t),("Content-Length",show r.length)]

echo :
     Socket AF_INET
  -> HTTPPull ByteString (Maybe Request)
  -> AsyncPull Poll Void [Errno] Bool
echo cli p =
  extractErr HTTPErr (writeTo cli (p >>= response)) >>= \case
    Left _  => (emit badRequest |> writeTo cli) $> False
    Right b => pure b
```

The only difference to the previous version is the boolean flag
we use to figure out if we got an empty message or not. With
this we can change `serve` in such a way that it loops until
the connection has been closed:

```idris
covering
serve : Socket AF_INET -> Async Poll [] ()
serve cli = guarantee tillFalse (close' cli)
  where
    covering
    tillFalse : Async Poll [] ()
    tillFalse =
      pull (bytes cli 0xfff |> request |> echo cli) >>= \case
        Succeeded False => pure ()
        Succeeded True  => cede >> tillFalse
        Error (Here x)  => stderrLn "\{x}"
        Canceled        => pure ()
```

Please note the call to `cede` before we loop and wait for a new
request: This will cause the current fiber to be rescheduled, so that
other fibers will have a chance to run first. This is all about fairness,
since we do not want a few connections with many requests to cause
all other connections to starve. Feel free to play around with this by
testing the behavior of the server under high load with and without
the call to `cede`.


The rest is the same as before:

```idris
addr : Bits16 -> IP4Addr
addr = IP4 [127,0,0,1]

covering
echoSrv : Bits16 -> (n : Nat) -> (0 p : IsSucc n) => Prog [Errno] Void
echoSrv port n =
  foreachPar n serve (acceptOn AF_INET SOCK_STREAM (addr port))

covering
prog : List String -> Prog [Errno] Void
prog ["server", port, n] =
  case cast {to = Nat} n of
    S k => echoSrv (cast port) (S k)
    0   => echoSrv (cast port) 128
prog _ = echoSrv 2222 128

covering
main : IO ()
main = do
  _ :: t <- getArgs | [] => runProg (prog [])
  runProg (prog t)
```


<!-- vi: filetype=idris2:syntax=markdown
-->
