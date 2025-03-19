module FS.Elin

import public Control.Monad.Elin
import public FS.Pull

import Data.SnocList

%default total

||| Convenience alias of `run` for running a `Pull` in the `Elin s`
||| monad, producing a pure result of type `Outcome es r`.
export %inline covering
pullElin : (forall s . EmptyPull (Elin s) es r) -> Outcome es r
pullElin f = either absurd id $ runElin (pull f)

||| Convenience alias of `run` for running a `Pull` in the `Elin s`
||| monad, producing a pure result.
export %inline covering
mpullElin : Monoid r => (forall s . EmptyPull (Elin s) [] r) -> r
mpullElin f = either absurd id $ runElin (mpull f)

export %inline covering
toSnocList : (forall s . Stream (Elin s) [] o) -> SnocList o
toSnocList p = mpullElin (foldC (:<) [<] p)

export %inline covering
toList : (forall s . Stream (Elin s) [] o) -> List o
toList p = toSnocList p <>> []
