module FS.Scope

import Data.Linear.Deferred
import Data.Linear.ELift1
import Data.Linear.Ref1
import Data.Linear.Unique
import Data.Maybe
import Data.SortedMap

%default total

export
record ScopeID where
  constructor SID
  val : Nat

export %inline
RootID : ScopeID
RootID = SID 0

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
record Scope (s : Type) (f : List Type -> Type -> Type) where
  constructor S
  ||| this scope's unique identifier
  id        : ScopeID

  ||| parent scopes `([parent, grand-parent, ... , root])`
  ancestors : List ScopeID

  ||| optional cleanup hook for a resource allocated in this scope
  cleanup   : List (f [] ())

  ||| list of child scopes
  children  : List ScopeID

||| The overall state of scopes.
public export
record ScopeST (s : Type) (f : List Type -> Type -> Type) where
  constructor SS
  index         : Nat
  scopes        : SortedMap ScopeID (Scope s f)

||| Returns the scope at the given scope ID.
export %inline
scopeAt : ScopeID -> ScopeST s f -> Maybe (Scope s f)
scopeAt n = lookup n . scopes

||| There is always a `root` scope, which is the parent of
||| of all scopes.
export %inline
getRoot : ScopeST s f -> Scope s f
getRoot ss = fromMaybe (S RootID [] [] []) (scopeAt RootID ss)

||| Deletes the scope at the given scope ID.
|||
||| When the scope in question is the root scope (ID 0),
||| only field `rootChildren` is reset to the empty list.
export %inline
deleteAt : ScopeID -> ScopeST s f -> ScopeST s f
deleteAt n = {scopes $= delete n}

||| Inserts a new scope. In case of the root scope, field
||| `rootChildren` is adjusted.
export %inline
insertScope : Scope s f -> ScopeST s f -> ScopeST s f
insertScope s = {scopes $= insert s.id s}

||| Finds the closest ancestor scope that is still open.
|||
||| Note: The `root` scope cannot be fully closed, so this will always
|||       return a sope.
export
openAncestor : ScopeST s f -> Scope s f -> Scope s f
openAncestor ss = go . ancestors
  where
    go : List ScopeID -> Scope s f
    go []        = getRoot ss
    go (x :: xs) = fromMaybe (go xs) (scopeAt x ss)

||| Returns the given scope if it is still open or its closest ancestor.
|||
||| Note: The `root` scope cannot be fully closed, so this will always
|||       return a sope.
export
openSelfOrAncestor : ScopeST s f -> Scope s f -> Scope s f
openSelfOrAncestor ss sc =
  fromMaybe (openAncestor ss sc) (scopeAt sc.id ss)

-- utility alias
0 FScope : (s : Type) -> (f : List Type -> Type -> Type) -> Type -> Type
FScope s f a = ScopeST s f -> (ScopeST s f, a)

-- creates a new child scope with the given cleanup hook
-- for the given parent scope.
scope : List (f [] ()) -> Scope s f -> FScope s f (Scope s f)
scope cleanup par ss =
  let ancs := par.id :: par.ancestors
      sc   := S (SID ss.index) ancs cleanup []
      par2 := {children $= (sc.id ::)} par
      ss2  := insertScope par2 $ insertScope sc ss
   in ({index $= S} ss2, sc)

||| Initial state of scopes.
export
empty : ScopeST s f
empty = SS 1 empty

parameters {0    f   : List Type -> Type -> Type}
           {auto eff : ELift1 s f}
           (ref      : Ref s (ScopeST s f))

  ||| Returns the current state of the root scope
  export %inline
  root : f es (Scope s f)
  root = getRoot <$> readref ref

  ||| Opens and returns a new child scope for the given parent
  ||| scope.
  |||
  ||| The optional `Bool` effect is used for checking for interruption.
  |||
  ||| If the parent scope has already been closed, its closest
  ||| open ancestor will be used as the new scope's parent instead.
  export
  openScope : Scope s f -> f es (Scope s f)
  openScope par = do
    update ref $ \ss =>
      scope [] (openSelfOrAncestor ss par) ss

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
      case scopeAt id ss of
        Nothing => (ss, pure ())
        Just sc => (deleteAt id ss, closeAll sc.children sc.cleanup)
    act

  ||| Lookup the scope with the given ID.
  export %inline
  findScope : ScopeID -> f es (Maybe $ Scope s f)
  findScope id = lookup id . scopes <$> readref ref

  ||| Adds a new cleanup hook to the given scope or its closest
  ||| open parent scope.
  export %inline
  addHook : Scope s f -> f [] () -> f es (Scope s f)
  addHook sc hook =
    Ref1.update ref $ \ss =>
     let res := {cleanup $= (hook ::)} (openSelfOrAncestor ss sc)
      in (insertScope res ss, res)
