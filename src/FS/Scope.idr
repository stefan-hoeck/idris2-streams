module FS.Scope

import Control.Monad.Elin

import Data.Linear.Deferred
import Data.Linear.ELift1
import Data.Linear.Ref1
import Data.Linear.Unique
import Data.Maybe
import Data.SortedMap

import IO.Async

%default total

--------------------------------------------------------------------------------
-- Interrupt
--------------------------------------------------------------------------------

||| An interruption handler.
|||
||| This is used for cross-stream interruption when running streams in
||| parallel. For instance, when nondeterministically merging two streams
||| A and B (see `FS.Concurrent.merge`), A and B will be run in parallel
||| each on its own fiber. Both should be interrupted if downstream terminates,
||| for instance because the number of emitted values have been limited via
||| a call to `take`.
|||
||| Implementation detail: When running a stream, we check on each iteration
||| whether the current scope has been interrupted or not. In addition, in
||| case of wrapped effectful computations - which might be potentially long
||| running (think of a timer or waiting for a connection or a mouse click) -
||| the wrapped effect is raced against `awaitInterruption`.
public export
data Interrupt : (f : List Type -> Type -> Type) -> Type where
  None : Interrupt f
  I    : (def : Deferred World a) -> Interrupt (Async e)

--------------------------------------------------------------------------------
-- Scopes
--------------------------------------------------------------------------------

||| IDs for comparing and ordering scopes. This is for internal
||| use only. In particular, looking at the internal representation
||| of a `ScopeID` via `Show` is *not* referentially transparent and
||| should be used for debugging purposes only.
export
record ScopeID where
  constructor SID
  val : Nat

export %inline
Eq ScopeID where
  SID x == SID y = x == y

export %inline
Ord ScopeID where
  compare (SID x) (SID y) = compare x y

export %inline
Show ScopeID where
  show = show . val

||| Cancelation scopes
|||
||| Functional streams are evaluated in scopes, which are organized as
||| a tree, just like stream evaluation can be thought of as a tree:
||| Sequencing of streams means nesting in the resulting scope tree,
||| while parallel evaluation (for instance, when zipping or merging
||| streams) means branching. Once a stream is exhausted,
||| it's scope is cleaned up and all resources allocated in this scope
||| are released, including the resources of all child scope.
|||
||| In addition to (internal) cancelation, streams can be run concurrently,
||| in which case the can be interrupted by an external event such as
||| the exhaustion of a timer or the termination of another stream.
||| At every evaluation step of a stream we check, if the current scope
||| has been canceled. If this is the case, evaluation of the stream
||| is aborted.
|||
||| Just like `Pull`s and `Stream`s, a `Scope` is parameterized by its
||| effect type.
public export
record Scope (f : List Type -> Type -> Type) where
  constructor S
  ||| this scope's unique identifier
  id        : ScopeID

  ||| ID of this scope's root scope
  root      : ScopeID

  ||| parent scopes `([parent, grand-parent, ... , root])`
  ancestors : List ScopeID

  ||| optional cleanup hook for a resource allocated in this scope
  cleanup   : List (f [] ())

  ||| list of child scopes
  children  : List ScopeID

  ||| Handler to check for stream interruption
  interrupt : Interrupt f

||| State of scopes of a running stream.
public export
0 ScopeST : (f : List Type -> Type -> Type) -> Type
ScopeST f = SortedMap ScopeID (Scope f)

--------------------------------------------------------------------------------
-- Compilation Targets
--------------------------------------------------------------------------------

||| Target effect of stream compilation.
|||
||| Effect type `f` (of type `List Type -> Type -> Type`) can be used to
||| run (= evaluate) streams in state thread `s`.
||| Currently, this is either `Elin s` for running synchronous streams in state
||| effect `s`, or `Async e` for running streams concurrently.
|||
||| If `s` is universally quantified, `Elin s` streams can be converted to pure
||| functions making use of local mutable state, resource management, and error
||| handling. If `s` equals `World`, `Elin World` can be used as a regular
||| (synchronous) monad with error handling.
public export
interface ELift1 s f => Target s f | f where

  ||| Initial scope reference for running a stream.
  scopes : f es (Ref s (ScopeST f))

  ||| Combines two interruption handlers
  combineInterrupts : (x,y : Interrupt f) -> f es (Interrupt f, List (f [] ()))

  ||| Returns `True` if the stream has been interrupted.
  isInterrupted : Interrupt f -> f es Bool

  ||| Races an effectful computation against stream interruption
  raceInterrupt : Interrupt f -> f es a -> f es (Maybe a)

export %inline
Target s (Elin s) where
  scopes = newref empty
  combineInterrupts None None = pure (None, [])
  isInterrupted _ = pure False
  raceInterrupt _ act = map Just act

%noinline
asyncScopes : IORef (ScopeST $ Async e)
asyncScopes = unsafePerformIO $ newref empty

export
Target World (Async e) where
  scopes = pure asyncScopes

  combineInterrupts None   x      = pure (x, [])
  combineInterrupts x      None   = pure (x, [])
  combineInterrupts (I d1) (I d2) = do
    d3 <- deferredOf ()
    f1 <- start {es = []} (await d1 >>= \_ => putDeferred d3 ())
    f2 <- start {es = []} (await d2 >>= \_ => putDeferred d3 ())
    pure (I d3, [cancel f1 >> cancel f2])

  isInterrupted None  = pure False
  isInterrupted (I d) = completed d

  raceInterrupt None  act = map Just act
  raceInterrupt (I d) act =
    (>>= either Just (const Nothing)) <$> race2 act (await d)

--------------------------------------------------------------------------------
-- Handling Scopes
--------------------------------------------------------------------------------

||| There is always a `root` scope, which is the parent of
||| of all scopes.
export %inline
getRoot : ScopeID -> ScopeST f -> Scope f
getRoot id = fromMaybe (S id id [] [] [] None) . lookup id

||| Inserts a new scope. In case of the root scope, field
||| `rootChildren` is adjusted.
export %inline
insertScope : Scope f -> ScopeST f -> ScopeST f
insertScope s = insert s.id s

||| Finds the closest ancestor scope that is still open.
|||
||| Note: The `root` scope cannot be fully closed, so this will always
|||       return a sope.
export
openAncestor : ScopeST f -> Scope f -> Scope f
openAncestor ss s = go s.ancestors
  where
    go : List ScopeID -> Scope f
    go []        = getRoot s.root ss
    go (x :: xs) = fromMaybe (go xs) (lookup x ss)

||| Returns the given scope if it is still open or its closest ancestor.
|||
||| Note: The `root` scope cannot be fully closed, so this will always
|||       return a sope.
export
openSelfOrAncestor : ScopeST f -> Scope f -> Scope f
openSelfOrAncestor ss sc =
  fromMaybe (openAncestor ss sc) (lookup sc.id ss)

parameters {0    f   : List Type -> Type -> Type}
           {auto tgt : Target s f}
           (ref      : Ref s (ScopeST f))

  ||| Returns the current state of the root scope
  export %inline
  root : f es (Scope f)
  root = do
    rid <- (SID . unsafeVal) <$> token
    let r := S rid rid [] [] [] None
    mod ref (insertScope r)
    pure r

  ||| Opens and returns a new child scope for the given parent
  ||| scope.
  |||
  ||| If the parent scope has already been closed, its closest
  ||| open ancestor will be used as the new scope's parent instead.
  export
  openScope : Interrupt f -> Scope f -> f es (Scope f)
  openScope int par = do
    sid          <- (SID . unsafeVal) <$> token
    (sint, cncl) <- combineInterrupts par.interrupt int
    update ref $ \ss =>
      let ancs := par.id :: par.ancestors
          sc   := S sid par.root ancs cncl [] sint
          par2 := {children $= (sc.id ::)} par
       in (insertScope par2 $ insertScope sc ss, sc)

  ||| Closes the scope of the given ID plus all its child scopes,
  ||| releasing all allocated resources in reverse order of allocation
  ||| along the way.
  export
  close : ScopeID -> f [] ()

  closeAll : List ScopeID -> List (f [] ()) -> f [] ()
  closeAll []        cl = sequence_ cl
  closeAll (x :: xs) cl = assert_total $ close x >> closeAll xs cl

  close id = do
    act <- update ref $ \ss =>
      case lookup id ss of
        Nothing => (ss, pure ())
        Just sc => (delete id ss, closeAll sc.children sc.cleanup)
    act

  ||| Lookup the scope with the given ID.
  export %inline
  findScope : ScopeID -> f es (Maybe $ Scope f)
  findScope id = lookup id <$> readref ref

  ||| Adds a new cleanup hook to the given scope or its closest
  ||| open parent scope.
  export %inline
  addHook : Scope f -> f [] () -> f es (Scope f)
  addHook sc hook =
    Ref1.update ref $ \ss =>
     let res := {cleanup $= (hook ::)} (openSelfOrAncestor ss sc)
      in (insertScope res ss, res)

||| Creates a new root scope and returns it together with the set of
||| scopes for the given effect type.
export %inline
newScope : Target s f => f es (Scope f, Ref s (ScopeST f))
newScope = do
  ref <- scopes
  sc  <- root ref
  pure (sc, ref)
