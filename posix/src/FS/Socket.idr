module FS.Socket

import public FS.Posix
import public IO.Async.Socket
import IO.Async.Loop.Posix

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

  acceptMany : Nat -> Socket d -> Async e es (List $ Socket d)
  acceptMany n sock = do
    c <- acceptnb sock
    go [<c] n

    where
      go : SnocList (Socket d) -> Nat -> Async e es (List $ Socket d)
      go ss 0     = pure (ss <>> [])
      go ss (S k) =
        attempt (accept {es = [Errno]} sock) >>= \case
          Right peer    => go (ss :< peer) k
          Left (Here x) =>
            if x == EINPROGRESS || x == EAGAIN
               then pure (ss <>> [])
               else throw x

  export
  acceptN : Nat -> (d : Domain) -> SockType -> Addr d -> AsyncStream e es (List $ Socket d)
  acceptN n d tpe addr =
    resource ((\x => Socket.R x) <$> socketnb d tpe) $ \(R sock) => do
      bind sock addr
      listen sock 2048
      repeat $ eval (acceptMany n sock)
