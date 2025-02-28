module FS.Elin

import public Control.Monad.Elin
import public FS.Stream
import FS.Pull

%default total

fromOutcome : Monoid a => Outcome [] a -> a
fromOutcome (Succeeded res) = res
fromOutcome Canceled        = neutral
fromOutcome (Error err)     = absurd err

||| Runs a `Pull` to completion, collecting all output in a list.
export covering
pullListRes : (forall s . Pull s (Elin s) o es ()) -> Outcome es (List o)
pullListRes p = pullElin ((<>> []) <$> foldChunks [<] (<><) p)

||| Like `pullListRes`, but without the possibility of failure.
export covering
pullList : (forall s . Pull s (Elin s) o [] ()) -> List o
pullList p = fromOutcome $ pullListRes p

||| Runs a `Pull` to completion, collecting all chunks of output in a list.
||| This allows us to observe the chunk structure of a `Pull`.
export covering
pullChunkRes : (forall s . Pull s (Elin s) o es ()) -> Outcome es (List $ List o)
pullChunkRes p = pullElin ((<>> []) <$> foldChunks [<] (:<) p)

||| Like `echunks`, but without the possibility of failure.
export covering
pullChunks : (forall s . Pull s (Elin s) o [] ()) -> List (List o)
pullChunks p = fromOutcome $ pullChunkRes p

||| Runs a `Stream` to completion, collecting all output in a list.
export covering
streamListRes : (forall s . Stream s (Elin s) es o) -> Outcome es (List o)
streamListRes p = either absurd id $ runElin (toList p)

||| Like `streamListRes`, but without the possibility of failure.
export covering
streamList : (forall s . Stream s (Elin s) [] o) -> List o
streamList p = fromOutcome $ streamListRes p

||| Runs a `Stream` to completion, collecting all chunks of output in a list.
||| This allows us to observe the chunk structure of a `Stream`.
export covering
streamChunkRes : (forall s . Stream s (Elin s) es o) -> Outcome es (List $ List o)
streamChunkRes p = either absurd id $ runElin (toChunks p)

||| Like `echunks`, but without the possibility of failure.
export covering
streamChunks : (forall s . Stream s (Elin s) [] o) -> List (List o)
streamChunks p = fromOutcome $ streamChunkRes p

export covering
runIO : Stream World (Elin World) [] () -> IO ()
runIO = ignore . runElinIO . run
