# A basic HTTP Server

```idris
module HTTP

import Data.SortedMap
import Derive.Prelude
import FS.Posix

import IO.Async.Loop.Posix

%default total
%language ElabReflection

public export
data Method = GET | POST

%runElab derive "Method" [Show,Eq,Ord]

public export
record Request where
  constructor R
  method  : Method
  uri     : String
  headers : SortedMap String String
  body    : AsyncStream Poll [Errno] ByteString

splitAtBytes :
     ByteString
  -> Pull f ByteString es o
  -> Pull f ByteString es (Pull f ByteString es o)

export
request : AsyncStream Poll [Errno] ByteString -> AsyncStream Poll [Errno] Request
request p =
  let spl := splitAtBytes "\r\n\r\n" p
   in ?fooo
```

<!-- vi: filetype=idris2:syntax=markdown
-->
