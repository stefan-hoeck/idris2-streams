# A basic HTTP Server

In this part of the tutorial, we are going to implement a basic
HTTP echo server that just echos the content of any `GET`
request back to the client. We are going to look at how
to split a stream of data at strategic locations and process
different parts of the stream individually. Let's get started.

```idris
module HTTP

import public Data.SortedMap
import Derive.Prelude
import public FS.Posix
import public FS.Socket

import public IO.Async.Loop.Posix
import public IO.Async.Loop.Epoll

import public System

%default total
%language ElabReflection
```

To keep things simple, we start with HTTP 1.0 support only.
We are going to define a bunch of type aliases and utilities
before we start working on streaming HTTP requests:

```idris
public export
0 Prog : List Type -> Type -> Type
Prog = AsyncStream Poll

export covering
runProg : Prog [Errno] Void -> IO ()
runProg prog = epollApp $ mpull (handle [stderrLn . interpolate] prog)

public export
data HTTPErr : Type where
  HeaderSizeExceeded  : HTTPErr
  ContentSizeExceeded : HTTPErr
  InvalidRequest      : HTTPErr

%runElab derive "HTTPErr" [Show,Eq,Ord]

export
Interpolation HTTPErr where
  interpolate HeaderSizeExceeded  = "header size exceeded"
  interpolate ContentSizeExceeded = "content size exceeded"
  interpolate InvalidRequest      = "invalid HTTP request"

public export
0 HTTPPull : Type -> Type -> Type
HTTPPull o r = AsyncPull Poll o [Errno,HTTPErr] r

public export
0 HTTPStream : Type -> Type
HTTPStream o = AsyncPull Poll o [Errno,HTTPErr] ()
```

## A Data Type for HTTP Requests

First, we are going to define a `Request` data type and some
additional utilities. A typical HTTP request consists of a
start line listing the HTTP method, request target, and protocol to
use, followed by an arbitrary number of headers (colon-separated
name/value pairs, each on a separate line), followed by a final
empty line. After this follows the - optional - body of the message.

In HTTP 1.0, we typically need to fully process the start line and message
headers, because they contain detailed instructions about
what the client requests. The message body, however, could consist of
larger amounts of data that might not even fit into memory, so we
might not want to process that as a whole unless we know it is of
reasonable size.

Here are a couple of data types encapsulating all of this:

```idris
public export
0 Headers : Type
Headers = SortedMap String String

public export
data Method = GET | POST | HEAD

%runElab derive "Method" [Show,Eq,Ord]

public export
data Version = V10 | V11 | V20

%runElab derive "Version" [Show,Eq,Ord]

public export
record Request where
  constructor R
  method  : Method
  uri     : String
  version : Version
  headers : Headers
  length  : Nat
  type    : Maybe String
  body    : HTTPStream ByteString
```

As you can see, the request body is wrapped up as a byte stream for
later consumption.

## HTTP Streaming Strategy

The general strategy for processing a HTTP request coming in
as stream of bytes read from a TCP socket can be described as
follows:

* Split of the request header by streaming and accumulating
  chunks of bytes until an empty line (represented as '"\r\n\r\n"')
  is encountered.
* Split the header along line breaks and process the start line followed
  by the request headers.
* Analyze the request headers and process the body accordingly.
* Answer with a suitable response.

In addition to the above, we might consider putting a limit on the
size of the request header to make sure it conveniently fits into memory.
We should also limit size of the request body, depending on the kind of
data it contains. In a real application, such limits would be part
of a larger set of configuration settings but here we hard-code them
to keep things simple.

```idris
MaxHeaderSize : Nat
MaxHeaderSize = 0xffff

MaxContentSize : Nat
MaxContentSize = 0xffff_ffff
```

Here's a function for processing the start line of a HTTP request:

```idris
%inline
SPACE, COLON : Bits8
SPACE = 32
COLON = 58

method : String -> Either HTTPErr Method
method "GET"  = Right GET
method "POST" = Right POST
method "HEAD" = Right HEAD
method _      = Left InvalidRequest

version : String -> Either HTTPErr Version
version "HTTP/1.0" = Right V10
version "HTTP/1.1" = Right V11
version "HTTP/2.0" = Right V20
version _          = Left InvalidRequest

startLine : ByteString -> Either HTTPErr (Method,String,Version)
startLine bs =
  case toString <$> split SPACE (trim bs) of
    [m,t,v] => [| (\x,y,z => (x,y,z)) (method m) (pure t) (version v) |]
    _       => Left InvalidRequest

```

Next, we need a function to process and accumulate the request
headers, one line at a time. We simplify this a bit, since in
theory a header's value could be spread across several lines.
For now, we are not going to support this.

```idris
headers : List ByteString -> Headers -> Either HTTPErr Headers
headers []     hs = Right hs
headers (h::t) hs =
  case break (58 ==) h of -- 58 is a colon (:)
    (xs,BS (S k) bv) =>
     let name := toLower (toString xs)
         val  := toString (trim $ tail bv)
      in headers t (insert name val hs)
    _                => Left InvalidRequest
```

Given a stream of lists of byte vectors (each byte vector corresponding
to a single line of the request header), we can use `next` to accumulate
the set of headers:

In `accumHeaders`, we use `evalMap` to map the emitted values with
the possibility of failure and
`foldPair` to return the accumulate result together with the
other result of the pull. In case no set of headers was accumulated,
we abort with an error. Please note, that calling `foldPair` to accumulate
all values in a stream is somewhat risky especially if the result grows
with the number of accumulated values. We are safe here, however, since
we are going to limit the header to `MaxHeaderSize` bytes.

Next, we need the ability to extract values for a couple of specific
headers (header names in HTTP are case insensitive):

```idris
contentLength : Headers -> Nat
contentLength = maybe 0 cast . lookup "content-length"

contentType : Headers -> Maybe String
contentType = lookup "content-type"
```

We are now ready to assemble the HTTP request from a pull of
the correct shape:

```idris
parseHeader :
     ByteString
  -> HTTPStream ByteString
  -> Either HTTPErr (Maybe Request)
parseHeader (BS 0 bv) rem = Right Nothing
parseHeader (BS _ bv) rem =
  case ByteVect.lines bv of
    h::ls =>
      let Right (m,t,v) := startLine h      | Left x => Left x
          Right hs      := headers ls empty | Left x => Left x
          cl            := contentLength hs
          ct            := contentType hs
       in if cl > MaxContentSize
             then Left ContentSizeExceeded
             else Right $ Just (R m t v hs cl ct $ C.take cl rem)
    []    => Left InvalidRequest

accumHeader :
     SnocList ByteString
  -> HTTPPull ByteString (HTTPStream ByteString)
  -> HTTPPull o (Maybe Request)
accumHeader sb p =
  assert_total $ P.uncons p >>= \case
    Left x       => case sb of
      [<bs] => injectEither (parseHeader bs x)
      _     => injectEither (parseHeader (fastConcat $ sb <>> []) x)
    Right (bs,q) => accumHeader (sb:<bs) q
```

Function `checkLength` limits the number of remaining bytes we read
from the client to the content length given in the request header.
If this length exceeds our predefined size limit, we immediately throw
an exception and abort.

The actual stream processing is done in `assemble`: Given a pull that
emits the request header one line at a time and returns the remainder
of the byte stream containing the content body, we first extract the
start line and try to parse the HTTP method and request target. We
then accumulate the request headers by invoking `accumHeaders` and
return everything as the result of a pull that no longer emits any
values. A minor detail: Once we [start reusing connections](HTTP11.md)
we might receive an empty byte sequence as a sign that the connection
has been closed by the client. We deal with this by returning
nothing to signal that the corresponding socket needs to be
closed on our end as well.

The only thing missing is the splitting of the raw byte stream
into header and body. Here's the code:

```idris
export
request : HTTPStream ByteString -> HTTPPull o (Maybe Request)
request req =
     breakAtSubstring pure "\r\n\r\n" req
  |> C.limit HeaderSizeExceeded MaxHeaderSize
  |> accumHeader [<]
```

The header of a HTTP request is separated from the body by a
single empty line, so we split the whole input at the first occurrence
of the corresponding byte sequence. In addition, we limit the
size of the header to the predefined number of bytes and
split it along line breaks before passing everything to `assemble`.

## HTTP Response

A HTTP response resembles a request very closely, it being also separated into
a header and optional body. The start line lists the protocol we use
followed by a status code and an optional status message, which
we don't provide.

```idris
export
encodeResponse : (status : Nat) -> List (String,String) -> ByteString
encodeResponse status hs =
  fastConcat $ intersperse "\r\n" $ map fromString $
    "HTTP/1.1 \{show status}" ::
    map (\(x,y) => "\{x}: \{y}") hs ++
    ["\r\n"]

export
badRequest : ByteString
badRequest = encodeResponse 400 []

export
ok : List (String,String) -> ByteString
ok = encodeResponse 200

response : Maybe Request -> HTTPStream ByteString
response Nothing  = pure ()
response (Just r) = cons resp r.body
  where
    resp : ByteString
    resp = case r.type of
      Nothing => ok [("Content-Length",show r.length)]
      Just t  => ok [("Content-Type",t),("Content-Length",show r.length)]
```

As you can see, in order to echo the request body back to the client,
we just prepend (`cons`) a suitable response header to the corresponding
byte stream.

We are now ready to handle a single request from start to beginning:

```idris
echo :
     Socket AF_INET
  -> HTTPPull ByteString (Maybe Request)
  -> AsyncStream Poll [Errno] Void
echo cli p =
  extractErr HTTPErr (writeTo cli (p >>= response)) >>= \case
    Left _   => emit badRequest |> writeTo cli
    Right () => pure ()

covering
serve : Socket AF_INET -> Async Poll [] ()
serve cli =
  flip guarantee (close' cli) $
    mpull $ handleErrors (\(Here x) => stderrLn "\{x}") $
         bytes cli 0xfff
      |> request
      |> echo cli
```

As you can see, we added some error handling facilities and made
sure the client connection is properly closed once we are done.

## Accepting Connections

The final missing step is accepting incoming connections and
serving them, possibly in parallel and without blocking.
We can use the `foreachPar` combinator for processing values
produced by a stream in parallel.

```idris
addr : Bits16 -> IP4Addr
addr = IP4 [127,0,0,1]

covering
echoSrv : Bits16 -> (n : Nat) -> (0 p : IsSucc n) => Prog [Errno] Void
echoSrv port n =
  foreachPar n serve (acceptOn AF_INET SOCK_STREAM (addr port))
```

Below is a bit of glue code to read a couple of settings from
command-line arguments: The port we are listening on as well as
the maximum number of connections we serve in parallel.

```idris
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

With this simple HTTP server, we can already handle thousands
of requests per second. In order to speed things up even more,
we need to reuse connections, however, which inevitably leads
to HTTP 1.1. In the [next section](HTTP11.md) we are going
to make the necessary adjustments.

<!-- vi: filetype=idris2:syntax=markdown
-->
