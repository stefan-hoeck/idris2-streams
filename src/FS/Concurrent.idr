module FS.Concurrent

import Data.Linear.Ref1
import FS.Pull
import IO.Async.Loop.TimerH
import public FS.Stream
import public IO.Async

export
interruptWhen :
     Stream World (Async e) es o
  -> Stream World (Async e) [] Bool
  -> Stream World (Async e) es o
-- interruptWhen str stop =
--   force $ do
--     doneL <- newref False
--     doneR <- newref False
--     pure (watched doneL doneR)
--
--   where
--     watcher : (doneL, doneR : IORef Bool) -> Async e [] ()
--     watcher doneL doneR =
--       guarantee
--         (run $ ignore $ interruptRef doneL $ any id stop)
--         (writeref doneR True)
--
--     watched : (doneL, doneR : IORef Bool) -> Stream (Async e) es o
--     watched doneL doneR = S $ do
--       _ <- acquire (start $ watcher doneL doneR) (\_ => writeref doneL True)
--       pull (interruptRef doneR str)

export
timeout : TimerH e => Clock Duration -> Stream World (Async e) es o -> Stream World (Async e) es o
timeout dur str = str `interruptWhen` eval (sleep dur $> True)
