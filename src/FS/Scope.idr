module FS.Scope

import Data.Linear.ELift1
import Data.Linear.Ref1
import Data.Maybe
import Data.SortedMap

%default total

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
||| Just like `Pull`s and `Stream`s, a `Scope` is parameterized by its
||| effect type.
public export
record Scope (f : List Type -> Type -> Type) where
  constructor S
  ||| this scope's unique identifier
  id        : Nat

  ||| parent scopes `([parent, grand-parent, ... , root])`
  ancestors : List Nat

  ||| optional cleanup hook for a resource allocated in this scope
  cleanup   : Maybe (f [] ())

  ||| list of child scopes
  children  : List Nat

||| The overall state of scopes.
public export
record ScopeST (f : List Type -> Type -> Type) where
  constructor SS
  index        : Nat
  rootChildren : List Nat
  scopes       : SortedMap Nat (Scope f)

||| Initial state of scopes.
export
empty : ScopeST f
empty = SS 1 [] empty

||| There is always a `root` scope, which is the parent of
||| of all scopes.
export %inline
getRoot : ScopeST f -> Scope f
getRoot ss = S 0 [] Nothing ss.rootChildren

||| Returns the scope at the given scope ID.
export %inline
scopeAt : Nat -> ScopeST f -> Maybe (Scope f)
scopeAt 0 ss = Just (getRoot ss)
scopeAt n ss = lookup n ss.scopes

||| Deletes the scope at the given scope ID.
|||
||| When the scope in question is the root scope (ID 0),
||| only field `rootChildren` is reset to the empty list.
export %inline
deleteAt : Nat -> ScopeST f -> ScopeST f
deleteAt 0 = {rootChildren := []}
deleteAt n = {scopes $= delete n}

||| Inserts a new scope. In case of the root scope, field
||| `rootChildren` is adjusted.
export %inline
insertScope : Scope f -> ScopeST f -> ScopeST f
insertScope s =
  case s.id of
    0 => {rootChildren := s.children}
    n => {scopes $= insert n s}

||| Finds the closest ancestor scope that is still open.
|||
||| Note: The `root` scope cannot be fully closed, so this will always
|||       return a sope.
export
openAncestor : ScopeST f -> Scope f -> Scope f
openAncestor ss = go . ancestors
  where
    go : List Nat -> Scope f
    go []        = getRoot ss
    go (x :: xs) = fromMaybe (go xs) (scopeAt x ss)

||| Returns the given scope if it is still open or its closest ancestor.
|||
||| Note: The `root` scope cannot be fully closed, so this will always
|||       return a sope.
export
openSelfOrAncestor : ScopeST f -> Scope f -> Scope f
openSelfOrAncestor ss sc =
  fromMaybe (openAncestor ss sc) (scopeAt sc.id ss)

-- utility alias
0 FScope : (f : List Type -> Type -> Type) -> Type -> Type
FScope f a = ScopeST f -> (ScopeST f, a)

-- creates a new child scope with the given cleanup hook
-- for the given parent scope.
scope : Scope f -> Maybe (f [] ()) -> FScope f (Scope f)
scope par cln ss =
  let ancs := par.id :: par.ancestors
      sc   := S ss.index ancs cln []
      par2 := {children $= (sc.id ::)} par
      ss2  := insertScope par2 $ insertScope sc ss
   in ({index $= S} ss2, sc)

parameters {0    f   : List Type -> Type -> Type}
           {auto eff : ELift1 s f}
           (ref      : Ref s (ScopeST f))

  ||| Returns the current state of the root scope
  export %inline
  root : f es (Scope f)
  root = getRoot <$> readref ref

  ||| Opens and returns a new child scope for the given parent
  ||| scope and cleanup hook.
  |||
  ||| If the parent scope has already been closed, its closest
  ||| open ancestor will be used as the new scope's parent instead.
  export
  openScope : Scope f -> Maybe (f [] ()) -> f es (Scope f)
  openScope par fin =
    update ref $ \ss =>
      scope (openSelfOrAncestor ss par) fin ss

  ||| Closes the scope of the given ID plus all its child scopes,
  ||| releasing all allocated resources in reverse order of allocation
  ||| along the way.
  export
  close : Nat -> f [] ()

  closeAll : List Nat -> Maybe (f [] ()) -> f [] ()
  closeAll []        Nothing   = pure ()
  closeAll []        (Just cl) = cl
  closeAll (x :: xs) cl        =
    assert_total $ close x >> closeAll xs cl

  close id = do
    act <- update ref $ \ss =>
      case scopeAt id ss of
        Nothing => (ss, pure ())
        Just sc => (deleteAt id ss, closeAll sc.children sc.cleanup)
    act

  ||| Lookup the scope with the given ID.
  export %inline
  findScope : Nat -> f es (Maybe $ Scope f)
  findScope id = lookup id . scopes <$> readref ref
