module FS.System

import Data.Linear.ELift1
import System
import FS.Pull

%default total

export %inline
args : ELift1 World f => Stream f es (List String)
args = eval (lift1 $ ioToF1 getArgs)
