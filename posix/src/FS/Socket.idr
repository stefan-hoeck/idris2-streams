module FS.Socket

import public FS.Posix
import public IO.Async.Socket

%default total

public export
record RFD (a : Type) where
  constructor R
  file : a
  {auto isf : FileDesc a}

export %inline
Resource (Async e) (RFD a) where
  cleanup (R f) = stdoutLn "Closing \{show $ fileDesc f}" >> close' f

parameters {0    es  : List Type}
           {auto ph  : PollH e}
           {auto has : Has Errno es}

  export
  acceptOn : (d : Domain) -> SockType -> Addr d -> AsyncStream e es (Socket d)
  acceptOn d tpe addr =
    resource ((\x => Socket.R x) <$> socketnb d tpe) $ \(R sock) => do
      bind sock addr
      listen sock 2048
      repeat $ eval (acceptnb sock)
