module FS.Scope

import Control.Monad.Elin

import Data.Linear.Deferred
import Data.Linear.ELift1
import Data.Linear.Ref1
import Data.Linear.Unique
import Data.Maybe
import Data.SortedMap
import Data.SortedSet

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
||| the wrapped effect is raced against the stream being interrupted.
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

  ||| Handler to check for stream interruption
  interrupt : Interrupt f

-- a node in the scope graph
export
record Node (f : List Type -> Type -> Type) where
  constructor N
  ||| The immutable scope state.
  scope : Scope f

  ||| optional cleanup hook for a resource allocated in this scope
  cleanup   : List (f [] ())

  ||| list of child scopes
  children  : SortedSet ScopeID

||| State of scopes of a running stream.
public export
0 ScopeST : (f : List Type -> Type -> Type) -> Type
ScopeST f = SortedMap ScopeID (Node f)

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
  scopes : f [] (Ref s (ScopeST f))

  ||| Combines two interruption handlers
  combineInterrupts : (x,y : Interrupt f) -> F1 s (Interrupt f, List (f [] ()))

  ||| Returns `True` if the stream has been interrupted.
  isInterrupted : Interrupt f -> f [] Bool

  ||| Races an effectful computation against stream interruption
  raceInterrupt : Interrupt f -> f es a -> f [] (Outcome es a)

export %inline
Target s (Elin s) where
  scopes = newref empty
  combineInterrupts None None t = (None, []) # t
  isInterrupted _ = pure False
  raceInterrupt _ = map toOutcome . attempt

%noinline
asyncScopes : IORef (ScopeST $ Async e)
asyncScopes = unsafePerformIO $ newref empty

export
Target World (Async e) where
  scopes = pure asyncScopes

  combineInterrupts None   x      t = (x, []) # t
  combineInterrupts x      None   t = (x, []) # t
  combineInterrupts (I d1) (I d2) t =
    let d3 # t := deferredOf1 () t
        f1 # t := observeDeferred1 d1 (\_ => putDeferred1 d3 ()) t
        f2 # t := observeDeferred1 d2 (\_ => putDeferred1 d3 ()) t
     in (I d3, [lift1 f1, lift1 f2]) # t

  isInterrupted None  = pure False
  isInterrupted (I d) = completed d

  raceInterrupt None  act = toOutcome <$> attempt act
  raceInterrupt (I d) act =
    racePair {fs = []} act (await d) >>= \case
      Left  (o,x) => cancel x $> o
      Right (x,_) => cancel x $> Canceled

--------------------------------------------------------------------------------
-- Handling Scopes
--------------------------------------------------------------------------------

-- There is always a `root` scope, which is the parent of
-- of all scopes.
getRoot : ScopeID -> ScopeST f -> Node f
getRoot id = fromMaybe (N (S id id [] None) [] empty) . lookup id

-- Inserts a new scope. In case of the root scope, field
-- `rootChildren` is adjusted.
insertScope : Node f -> ScopeST f -> ScopeST f
insertScope s = insert s.scope.id s

-- Finds the closest ancestor scope that is still open.
--
-- Note: The `root` scope cannot be fully closed, so this will always
--       return a sope.
openAncestor : ScopeST f -> Scope f -> Node f
openAncestor ss s = go s.ancestors
  where
    go : List ScopeID -> Node f
    go []        = getRoot s.root ss
    go (x :: xs) = fromMaybe (go xs) (lookup x ss)

-- Returns the given scope if it is still open or its closest ancestor.
--
-- Note: The `root` scope cannot be fully closed, so this will always
--       return a sope.
openSelfOrAncestor : ScopeST f -> Scope f -> Node f
openSelfOrAncestor ss sc =
  fromMaybe (openAncestor ss sc) (lookup sc.id ss)

removeChild : Bool -> Scope f -> ScopeST f -> ScopeST f
removeChild False sc st = st
removeChild True  sc st =
 let par := openAncestor st sc
  in insertScope ({children $= delete sc.id} par) st

parameters {0    f   : List Type -> Type -> Type}
           {auto tgt : Target s f}
           (ref      : Ref s (ScopeST f))

  scopeID : F1 s ScopeID
  scopeID t = let tok # t := token1 t in SID (unsafeVal tok) # t

  -- Creates a new root scope
  root : F1 s (Scope f)
  root t =
    let sid # t := scopeID t
        r       := N (S sid sid [] None) [] empty
        _   # t := mod1 ref (insertScope r) t
     in r.scope # t

  ||| Opens and returns a new child scope for the given parent
  ||| scope.
  |||
  ||| If the parent scope has already been closed, its closest
  ||| open ancestor will be used as the new scope's parent instead.
  export
  openScope : Interrupt f -> Scope f -> F1 s (Scope f)
  openScope int sc t =
   let sid          # t := scopeID t
       (sint, cncl) # t := combineInterrupts sc.interrupt int t
    in casupdate1 ref (\ss =>
        let par  := openSelfOrAncestor ss sc
            ancs := sc.id :: sc.ancestors
            node := N (Scope.S sid sc.root ancs sint) cncl empty
            par2 := {children $= insert sid} par
         in (insertScope par2 $ insertScope node ss, node.scope)) t

  ||| Adds a new cleanup hook to the given scope or its closest
  ||| open parent scope.
  export %inline
  addHook : Scope f -> f [] () -> f [] ()
  addHook sc hook =
    Ref1.mod ref $ \ss =>
     let res := {cleanup $= (hook ::)} (openSelfOrAncestor ss sc)
      in insertScope res ss

  ||| Closes the scope of the given ID plus all its child scopes,
  ||| releasing all allocated resources in reverse order of allocation
  ||| along the way.
  export
  close : (removeFromParent : Bool) -> ScopeID -> f [] ()

  closeAll : List ScopeID -> List (f [] ()) -> f [] ()
  closeAll []        cl = sequence_ cl
  closeAll (x :: xs) cl = assert_total $ close False x >> closeAll xs cl

  close b id = do
    act <- update ref $ \ss =>
      case lookup id ss of
        Nothing => (ss, pure ())
        Just sc =>
         let ss2 := removeChild b sc.scope $ delete id ss
          in (ss2, closeAll (reverse $ Prelude.toList sc.children) sc.cleanup)
    act

||| Creates a new root scope and returns it together with the set of
||| scopes for the given effect type.
export %inline
newScope : Target s f => f [] (Scope f, Ref s (ScopeST f))
newScope = do
 ref <- scopes
 sc  <- lift1 (FS.Scope.root ref)
 pure (sc, ref)
