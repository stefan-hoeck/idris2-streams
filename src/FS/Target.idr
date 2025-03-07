module FS.Target

import Data.Linear.Ref1
import Data.Linear.Token
import FS.Scope

%default total

interface Lift1 s f => Target s f | f where
