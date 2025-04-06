module HTTP

import Data.ByteString
import Data.SortedMap
import Derive.Prelude
import FS.Posix
import FS.Socket

import IO.Async.Loop.Posix
import Util

import System

%default total
%language ElabReflection

public export
record Client where
  constructor C
  isOpen   : IORef Bool
  request  : IORef (List ByteString)
  response : IORef (SnocList ByteString)

export
mkClient : Lift1 World f => ByteString -> f Client
mkClient bs = Prelude.[| C (newref False) (newref [bs]) (newref [<]) |]

export
defaultClient : Lift1 World f => f Client
defaultClient = mkClient "GET / HTTP/1.0\r\nHost: localhost\r\nAccept: */*\r\n\r\n"

closeClient : Lift1 World f => Client -> f ()
closeClient c = writeref c.isOpen False

nextBytes : Lift1 World f => Client -> f (Maybe ByteString)
nextBytes c =
  readref c.request >>= \case
    h::t => writeref c.request t $> Just h
    []   => pure Nothing

clientBytes : ELift1 World f => Client -> Stream f es ByteString
clientBytes = unfoldEvalMaybe . nextBytes

clientWrite : ELift1 World f => Client -> Pull f ByteString es r -> Pull f Void es r
clientWrite c = foreach (\bs => lift1 $ mod1 c.response (:< bs))

printErr : Lift1 World f => Interpolation e => e -> f ()
printErr x = lift1 $ ioToF1 (stderrLn $ interpolate x)

export covering
runProg : MCancel f => Target World f => Stream f [Errno] Void -> f [] ()
runProg prog = mpull (handle [printErr] prog)

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
0 HTTPPull : (List Type -> Type -> Type) -> Type -> Type -> Type
HTTPPull f o r = Pull f o [Errno,HTTPErr] r

public export
0 HTTPStream : (List Type -> Type -> Type) -> Type -> Type
HTTPStream f o = Pull f o [Errno,HTTPErr] ()

public export
0 Headers : Type
Headers = SortedMap String String

public export
data Method = GET | POST | HEAD

%runElab derive "Method" [Show,Eq,Ord]

public export
record Request f where
  constructor R
  method  : Method
  uri     : String
  headers : Headers
  length  : Nat
  type    : Maybe String
  body    : HTTPStream f ByteString

MaxHeaderSize : Nat
MaxHeaderSize = 0xffff

MaxContentSize : Nat
MaxContentSize = 0xffff_ffff

startLine : ByteString -> Either HTTPErr (Method,String)
startLine bs =
  case toString <$> split 32 bs of
    [met,tgt,_] => case met of
      "GET"  => Right (GET, tgt)
      "POST" => Right (POST,tgt)
      "HEAD" => Right (HEAD,tgt)
      _      => Left InvalidRequest
    _ => Left InvalidRequest

contentLength : Headers -> Nat
contentLength = maybe 0 cast . lookup "content-length"

contentType : Headers -> Maybe String
contentType = lookup "content-type"

headers : List ByteString -> Headers -> Either HTTPErr Headers
headers []     hs = Right hs
headers (h::t) hs =
  case break (58 ==) h of -- 58 is a colon (:)
    (xs,BS (S k) bv) =>
     let name := toLower (toString xs)
         val  := toString (trim $ tail bv)
      in headers t (insert name val hs)
    _                => Left InvalidRequest

parseHeader :
     ByteString
  -> HTTPStream f ByteString
  -> Either HTTPErr (Request f)
parseHeader (BS _ bv) rem =
  case ByteVect.lines bv of
    h::ls =>
      let Right (met,tgt) := startLine h      | Left x => Left x
          Right hs        := headers ls empty | Left x => Left x
          cl              := contentLength hs
          ct              := contentType hs
       in if cl <= MaxContentSize
             then Left ContentSizeExceeded
             else Right (R met tgt hs cl ct $ C.take cl rem)
    []    => Left InvalidRequest

accumHeader :
     SnocList ByteString
  -> Nat
  -> HTTPPull f ByteString (HTTPStream f ByteString)
  -> HTTPPull f o (Request f)
accumHeader sb sz p =
  assert_total $ P.uncons p >>= \case
    Left x       => case sb of
      [<bs] => injectEither (parseHeader bs x)
      _     => injectEither (parseHeader (fastConcat $ sb <>> []) x)
    Right (bs,q) =>
     let sz2 := sz + bs.size
      in if sz2 > MaxHeaderSize
            then throw HeaderSizeExceeded
            else accumHeader (sb:<bs) sz2 q

request : MErr f => HTTPStream f ByteString -> HTTPPull f o (Request f)
request req =
     forceBreakAtSubstring InvalidRequest "\r\n\r\n" req
  |> accumHeader [<] 0

encodeResponse : (status : Nat) -> List (String,String) -> ByteString
encodeResponse status hs =
  fastConcat $ intersperse "\r\n" $ map fromString $
    "HTTP/1.0 \{show status}" ::
    map (\(x,y) => "\{x}: \{y}") hs ++
    ["\r\n"]

badRequest : ByteString
badRequest = encodeResponse 400 []

ok : List (String,String) -> ByteString
ok = encodeResponse 200

response : Request f -> HTTPStream f ByteString
response r = cons resp r.body
  where
    resp : ByteString
    resp = case r.type of
      Nothing => ok []
      Just t  => ok [("Content-Type",t),("Content-Length",show r.length)]

echo :
     {auto m : MErr f}
  -> {auto el : ELift1 World f}
  -> Client
  -> HTTPPull f ByteString (Request f)
  -> Stream f [Errno] Void
echo cli p =
  extractErr HTTPErr (clientWrite cli (p >>= response)) >>= \case
    Left _   => emit badRequest |> clientWrite cli
    Right () => pure ()

export
serve : Target World f => MCancel f => Client -> f [] ()
serve cli =
  assert_total $ mpull $ handleErrors (\(Here x) => printErr x) $
    finally (closeClient cli) $
         clientBytes cli
      |> request
      |> echo cli

export
prog : HasIO (f []) => Target World f => MCancel f => Nat -> f [] ()
prog n = do
  dur <- (delta $ repeat n (defaultClient >>= serve))
  lift1 $ ioToF1 $ stdoutLn (prettyNS $ toNano dur `div` cast n)
