module FS.System

import Data.Linear.ELift1
import System
import FS.Pull

%default total

export %inline
args : HasIO (f es) => Stream f es String
args = getArgs >>= emits
