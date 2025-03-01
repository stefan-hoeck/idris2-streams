module FS.System

import Data.Linear.ELift1
import System
import FS.Stream

%default total

export %inline
args : ELift1 World f => Stream World f es String
args = evals $ lift1 (ioToF1 getArgs)
