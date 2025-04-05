module Main

import Control.Monad.Elin
import FS
import HTTP
import IO.Async.Loop.Epoll
import IO.Async.Loop.Posix
import System

main : IO ()
-- main =
-- ignore $ runElinIO $ getArgs >>= \case
--   [_,n] => HTTP.prog (cast n)
--   _     => HTTP.prog 100
main =
  epollApp $ getArgs >>= \case
    [_,n] => HTTP.prog (cast n)
    _     => HTTP.prog 100
