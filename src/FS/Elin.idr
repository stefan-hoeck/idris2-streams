module FS.Elin

import public Control.Monad.Elin
import public FS.Stream
import FS.Pull

%default total

fromOutcome : Monoid a => Outcome es a -> Result es a
fromOutcome (Succeeded res) = Right res
fromOutcome (Error err)     = Left err
fromOutcome Canceled        = Right neutral

fromResult : Result [] a -> a
fromResult (Right res) = res
fromResult (Left err)  = absurd err

||| Runs a `Pull` to completion, collecting all output in a list.
export covering
pullListRes : (forall s . Pull (Elin s) o es ()) -> Result es (List o)
pullListRes p =
  fromOutcome $
    pullElin ((<>> []) <$> foldChunk [<] (\sc,v => sc <>< toList v) p)

||| Like `pullListRes`, but without the possibility of failure.
export covering
pullList : (forall s . Pull (Elin s) o [] ()) -> List o
pullList p = fromResult $ pullListRes p

||| Runs a `Pull` to completion, collecting all chunks of output in a list.
||| This allows us to observe the chunk structure of a `Pull`.
export covering
pullChunkRes : (forall s . Pull (Elin s) o es ()) -> Result es (List $ Chunk o)
pullChunkRes p = fromOutcome $ pullElin ((<>> []) <$> foldChunk [<] (:<) p)

||| Like `echunks`, but without the possibility of failure.
export covering
pullChunks : (forall s . Pull (Elin s) o [] ()) -> List (Chunk o)
pullChunks p = fromResult $ pullChunkRes p

||| Runs a `Stream` to completion, collecting all output in a list.
export covering
streamListRes : (forall s . Stream (Elin s) es o) -> Result es (List o)
streamListRes p = runElin (toList p)

||| Like `streamListRes`, but without the possibility of failure.
export covering
streamList : (forall s . Stream (Elin s) [] o) -> List o
streamList p = fromResult $ streamListRes p

||| Runs a `Stream` to completion, collecting all chunks of output in a list.
||| This allows us to observe the chunk structure of a `Stream`.
export covering
streamChunkRes : (forall s . Stream (Elin s) es o) -> Result es (List $ Chunk o)
streamChunkRes p = runElin (toChunks p)

||| Like `echunks`, but without the possibility of failure.
export covering
streamChunks : (forall s . Stream (Elin s) [] o) -> List (Chunk o)
streamChunks p = fromResult $ streamChunkRes p

export covering
runIO : Stream (Elin World) [] Void -> IO ()
runIO = ignore . runElinIO . run
