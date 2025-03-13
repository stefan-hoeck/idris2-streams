module FS.System

import Data.Linear.ELift1
import System
import FS.Stream

%default total

export %inline
args : ELift1 World f => Stream f es String
args = evalList $ lift1 (ioToF1 getArgs)
