module FS.Target

import Control.Monad.Elin
import Data.Linear.Ref1
import Data.Linear.Token
import Data.SortedMap
import FS.Scope
import IO.Async

%default total

public export
interface ELift1 s f => Target s f | f where
  scopes : f es (Ref s (ScopeST f))

export %inline
Target s (Elin s) where
  scopes = newref empty

%noinline
asyncScopes : IORef (ScopeST $ Async e)
asyncScopes = unsafePerformIO $ newref empty

export %inline
Target World (Async e) where
  scopes = pure asyncScopes

||| Creates a new root scope and returns it together with the set of
||| scopes for the given effect type.
export %inline
newScope : Target s f => f es (Scope f, Ref s (ScopeST f))
newScope = do
  ref <- scopes
  sc  <- root ref
  pure (sc, ref)
