module FS.Scope

import Control.Monad.Elin

import Data.Linear.Deferred
import Data.Linear.ELift1
import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.Linear.Unique
import Data.List
import Data.Maybe
import Data.Nat
import Data.SortedMap
import Data.SortedSet

import IO.Async

%default total

--------------------------------------------------------------------------------
-- Hook
--------------------------------------------------------------------------------

record Hook (f : List Type -> Type -> Type) where
  constructor H
  cleanup : f [] ()
  lease   : f [] (f [] ())

updCleanup, updUnlease : (Bool,Nat) -> ((Bool,Nat),Bool)
updCleanup (False,b) = ((True,b),b == 0)
updCleanup p         = (p,False)

updUnlease (b,1) = ((b,0),b)
updUnlease (b,n) = ((b,pred n),False)

updLease : (Bool,Nat) -> ((Bool,Nat),())
updLease (b,n) = ((b,S n),())

hook : ELift1 s f => f [] () -> F1 s (Hook f)
hook act t =
 let state # t := ref1 (False,Z) t -- (cleaned up, leased)
  in H (cl state) (ls state) # t

  where
    cl : Ref s (Bool,Nat) -> f [] ()
    cl state = when !(update state updCleanup) act

    unlease : Ref s (Bool,Nat) -> f [] ()
    unlease state = when !(update state updUnlease) act

    ls : Ref s (Bool,Nat) -> f [] (f [] ())
    ls state = update state updLease $> unlease state

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
  ||| Combines two interruption handlers
  combineInterrupts : (x,y : Interrupt f) -> F1 s (Interrupt f, List (f [] ()))

  ||| Returns `True` if the stream has been interrupted.
  isInterrupted : Interrupt f -> f [] Bool

  ||| Races an effectful computation against stream interruption
  raceInterrupt : Interrupt f -> f es a -> f [] (Outcome es a)

export %inline
Target s (Elin s) where
  combineInterrupts None None t = (None, []) # t
  isInterrupted _ = pure False
  raceInterrupt _ = map toOutcome . attempt

export
Target World (Async e) where
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

scopeID : F1 s ScopeID
scopeID t = let tok # t := token1 t in SID (unsafeVal tok) # t

export
record Node (f : List Type -> Type -> Type)

||| State of scopes of a running stream.
public export
0 ScopeST : (f : List Type -> Type -> Type) -> Type
ScopeST f = SortedMap ScopeID (Node f)

public export
0 STRef : (s : Type) -> (f : List Type -> Type -> Type) -> Type
STRef s f = Ref s (ScopeST f)

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
  {0 tstate : Type}

  ||| this scope's unique identifier
  id        : ScopeID

  ||| ID of this scope's root scope
  root      : ScopeID

  ||| parent scopes `([parent, grand-parent, ... , root])`
  ancestors : List ScopeID

  ||| Handler to check for stream interruption
  interrupt : Interrupt f

  state     : Ref tstate (ScopeST f)

  {auto tgt : Target tstate f}

-- a node in the scope graph
export
record Node (f : List Type -> Type -> Type) where
  constructor N
  ||| The immutable scope state.
  scope : Scope f

  ||| optional cleanup hook for a resource allocated in this scope
  cleanup   : List (Hook f)

  ||| list of child scopes
  children  : SortedSet ScopeID

--------------------------------------------------------------------------------
-- Handling Scopes
--------------------------------------------------------------------------------

-- Inserts a new scope. In case of the root scope, field
-- `rootChildren` is adjusted.
insertScope : Node f -> ScopeST f -> ScopeST f
insertScope s = insert s.scope.id s

-- There is always a `root` scope, which is the parent of
-- of all scopes.
getRoot : Target s f => STRef s f -> ScopeID -> ScopeST f -> Node f
getRoot ref id = fromMaybe (N (S id id [] None ref) [] empty) . lookup id

-- Finds the closest ancestor scope that is still open.
--
-- Note: The `root` scope cannot be fully closed, so this will always
--       return a sope.
openAncestor : ScopeST f -> Scope f -> Node f
openAncestor ss s@(S {}) = go s.ancestors
  where
    go : List ScopeID -> Node f
    go []        = getRoot s.state s.root ss
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

deleteNode : ScopeST f -> Node f -> ScopeST f
deleteNode m n = delete n.scope.id m

-- Creates a new root scope
root : Target s f => STRef s f -> F1 s (Scope f)
root ref t =
  let sid # t := scopeID t
      r       := N (S sid sid [] None ref) [] empty
      _   # t := mod1 ref (insertScope r) t
   in r.scope # t

||| Opens and returns a new child scope for the given parent
||| scope.
|||
||| If the parent scope has already been closed, its closest
||| open ancestor will be used as the new scope's parent instead.
export
openScope : Target s f =>  STRef s f -> Interrupt f -> Scope f -> F1 s (Scope f)
openScope ref int sc@(S i rt as ir _) t =
 let sid          # t := scopeID t
     (sint, cncl) # t := combineInterrupts ir int t
     hooks        # t := traverse1 hook cncl t
  in casupdate1 ref (\ss =>
      let par  := openSelfOrAncestor ss sc
          ancs := i :: as
          node := N (Scope.S sid rt ancs sint ref) hooks empty
          par2 := {children $= insert sid} par
       in (insertScope par2 $ insertScope node ss, node.scope)) t

||| Adds a new cleanup hook to the given scope or its closest
||| open parent scope.
export %inline
addHook : Scope f -> f [] () -> f [] ()
addHook sc@(S {}) act = do
  hk <- lift1 (hook act)
  Ref1.mod sc.state $ \ss =>
    let res := {cleanup $= (hk ::)} (openSelfOrAncestor ss sc)
     in insertScope res ss

parameters (ref : STRef s f)
  findNode : ScopeID -> F1 s (Maybe $ Node f)
  findNode x t = let st # t := read1 ref t in lookup x st # t

  findNodes : List ScopeID -> F1 s (List $ Node f)
  findNodes xs t = let ms # t := traverse1 findNode xs t in catMaybes ms # t

  childNodesL : List (Node f) -> List (Node f) -> F1 s (List (Node f))

  childNodes : List (Node f) -> Node f -> F1 s (List (Node f))
  childNodes ns n t =
   let ns2 # t := findNodes (reverse $ Prelude.toList n.children) t
    in childNodesL (n::ns) ns2 t

  childNodesL ns []      t = ns # t
  childNodesL ns (c::cs) t =
    assert_total $
     let ns2 # t := childNodes ns c t
      in childNodesL ns2 cs t

parameters {auto tgt : Target s f}
           (ref      : STRef s f)

  ||| Closes the scope of the given ID plus all its child scopes,
  ||| releasing all allocated resources in reverse order of allocation
  ||| along the way.
  export
  close : (remove : Bool) -> ScopeID -> f [] ()
  close b id = do
    Just n <- lift1 (findNode ref id) | Nothing => pure ()
    cs     <- lift1 (childNodes ref [] n)
    mod ref $ \m => removeChild b n.scope (foldl deleteNode m cs)
    traverse_ cleanup (cs >>= cleanup)

||| Leases all cleanup hooks from this scope as well as its direct
||| children and ancestors.
|||
||| Invoke the given action to release them again.
export
lease : Scope f -> f [] (f [] ())
lease sc@(S i r as is ref) = do
  Just nd <- lift1 (findNode ref i) | Nothing => pure (pure ())
  ns      <- lift1 (findNodes ref as)
  all     <- lift1 (childNodes ref ns nd)
  cs      <- traverse lease (all >>= cleanup)
  pure (sequence_ cs)

||| Creates a new root scope and returns it together with the set of
||| scopes for the given effect type.
export %inline
newScope : Target s f => f [] (Scope f)
newScope = do
  ref <- newref {a = ScopeST f} empty
  sc  <- lift1 (FS.Scope.root ref)
  pure sc

--------------------------------------------------------------------------------
-- Debugging Utilities
--------------------------------------------------------------------------------

export
printScope : Scope f -> String
printScope (S i _ as _ _) = fastConcat . intersperse " <- " . map show $ i::as

export %inline
Interpolation (Scope f) where interpolate = printScope

export
logScope : HasIO (f es) => String -> Scope f -> f es ()
logScope nm sc = putStrLn "Scope \{nm}: \{sc}"
