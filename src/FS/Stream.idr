module FS.Stream

import public Data.Linear.ELift1

import Data.List
import Data.Maybe
import Data.Nat
import FS.Pull

%default total

||| A `Stream f es o` is a newtype wrapper around a `Pull f o es ()`.
|||
||| Unlike a `Pull`, which is used to sequence computations with regard
||| to the pull's final result, a `Stream` effectfully produces a
||| sequence of values, similar to a list. Likewise, as with lists,
||| the monad implementation creates new streams from emitted values and
||| joins them.
|||
||| So, for a `Pull`, running the following code produces the values
||| `[1,2,3,4,5,6]`:
|||
||| ```idris
||| output [1,2,3] >> output [4,5,6]
||| ```
|||
||| while the following `Stream` produces the values `[4,5,6,4,5,6,4,5,6]`:
|||
||| ```idris
||| ignore (emits [1,2,3]) >> emits [4,5,6]
||| ```
public export
record Stream (f : List Type -> Type -> Type) (es : List Type) (o : Type) where
  constructor S
  pull : Pull f o es ()

--------------------------------------------------------------------------------
-- Interfaces
--------------------------------------------------------------------------------

export %inline
MErr (Stream f) where
  succeed      = S . output1
  fail         = S . fail
  bind (S v) f = S $ bindOutput1 (pull . f) v
  attempt      = S . attemptOutput . pull

export %inline
Semigroup (Stream f es o) where
  S p <+> S q = S $ p >> q

export %inline
Monoid (Stream f es o) where
  neutral = S (pure ())

export %inline
ELift1 s f => ELift1 s (Stream f) where
  elift1 act = S (elift1 act >>= output1)

--------------------------------------------------------------------------------
-- Creating Streams
--------------------------------------------------------------------------------

||| Returns a stream that emits a single value
export %inline
emit : o -> Stream f es o
emit = S . output1

||| Returns a stream that emits the given list of values (as a
||| single chunk).
export %inline
emits : List o -> Stream f es o
emits = S . output

||| Creates a single element stream that gets its value by evaluating the
||| supplied effect. If the effect fails, the returned stream fails.
export %inline
eval : f es o -> Stream f es o
eval act = S (Eval act >>= output1)

||| Like `eval` but emits the result as a single chunk
export %inline
evals : f es (List o) -> Stream f es o
evals act = S (Eval act >>= output)

export %inline
evalFoldable : Foldable m => f es (m o) -> Stream f es o
evalFoldable act = S (Eval act >>= foldable)

||| Creates a stream by successively applying
||| the given generator function to the threaded state
||| until a `Nothing` is returned
export %inline
unfold : (init : s) -> (s -> Maybe (o,s)) -> Stream f es o
unfold init g = S $ unfoldMaybe init g

||| Like `unfoldMaybe` but emits values in chunks.
export %inline
unfoldChunk : (init : s) -> (s -> (List o, Maybe s)) -> Stream f es o
unfoldChunk init g = S $ unfoldChunkMaybe init g

export %inline
unfoldEval : (init : s) -> (s -> f es (Maybe (o,s))) -> Stream f es o
unfoldEval init g = S $ unfoldEvalMaybe init g

||| Infinitely repeats the given stream.
export
repeat : Stream f es o -> Stream f es o
repeat (S v) = S $ repeat v

||| An infinite stream constantly emitting the given value
||| in chunks of the given size.
export
constant : o -> (size : Nat) -> Stream f es o
constant v size = repeat (emits $ replicate size v)

export
iterate : o -> (o -> o) -> Stream f es o
iterate v f = unfold v (\x => Just (x, f x))

export %inline
stream : Pull f o es () -> Stream f es o
stream p = S (OScope p Nothing)

export %inline
scope : Stream f es o -> Stream f es o
scope = stream . pull

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------

||| Prepends a chunk of values to the front of a stream
export %inline
cons : List o -> Stream f es o -> Stream f es o
cons vs = S . cons vs . pull

||| Prepends a single value to the front of a stream
export %inline
cons1 : o -> Stream f es o -> Stream f es o
cons1 = cons . pure

||| Alias for `(<+>)`
export %inline
(++) : Stream f es o -> Stream f es o -> Stream f es o
(++) = (<+>)

||| Emits the first `n` values of a stream
export %inline
take : Nat -> Stream f es o -> Stream f es o
take n = stream . ignore . take n . pull

export
replicate : Nat -> o -> Stream f es o
replicate n v =
  if n <= 0xff then emits (replicate n v) else take n (constant v 0xff)

||| Emits the last `n` values of a stream
export
takeRight : (n : Nat) -> (0 p : IsSucc n) => Stream f es o -> Stream f es o
takeRight n (S p) = S $ takeRight n p >>= output

||| Emits values until the given predicate returns `False`.
export %inline
takeWhile : (o -> Bool) -> Stream f es o -> Stream f es o
takeWhile pred = stream . ignore . takeWhile pred . pull

||| Like `takeWhile` but also includes the first failure.
export %inline
takeThrough : (o -> Bool) -> Stream f es o -> Stream f es o
takeThrough pred = stream . ignore . takeThrough pred . pull

||| Drops `n` elements of the input, then echoes the rest.
export
drop : Nat -> Stream f es o -> Stream f es o
drop n (S p) = S $ drop n p >>= fromMaybe (pure ())

||| Drops values from a stream while the given predicate returns `True`,
||| then echoes the rest.
export
dropWhile : (o -> Bool) -> Stream f es o -> Stream f es o
dropWhile pred (S p) = S $ dropWhile pred p >>= fromMaybe (pure ())

||| Like `dropWhile` but also drops the first value where
||| the predicate returns `False`.
export
dropThrough : (o -> Bool) -> Stream f es o -> Stream f es o
dropThrough pred (S p) = S $ dropThrough pred p >>= fromMaybe (pure ())

||| Chunk-wise maps the values produced by a stream
export %inline
mapChunks : (List o -> List p) -> Stream f es o -> Stream f es p
mapChunks f = S . mapChunks f . pull

||| Emits only inputs which match the supplied predicate.
export %inline
filter : (o -> Bool) -> Stream f es o -> Stream f es o
filter pred = S . filter pred . pull

||| Emits only inputs which do not match the supplied predicate.
filterNot : (o -> Bool) -> Stream f es o -> Stream f es o
filterNot pred = filter (not . pred)

||| Emits only inputs for which the given function returns a `Just`
export %inline
mapMaybe : (o -> Maybe p) -> Stream f es o -> Stream f es p
mapMaybe = mapChunks . mapMaybe

||| Emits the chunks of the input stream.
export %inline
chunks : Stream f es o -> Stream f es (List o)
chunks = mapChunks pure

||| Alias for `s >>= eval . f`
export %inline
evalMap : (o -> f es p) -> Stream f es o -> Stream f es p
evalMap f s = s >>= eval . f

||| Like `evalMap`, but operates on chunks for performance.
export
evalMapChunk :
     {auto app : Applicative (f es)}
  -> (o -> f es p)
  -> Stream f es o
  -> Stream f es p
evalMapChunk g s = chunks s >>= evals . traverse g

||| Chunk-wise folds all inputs using an initial
||| value and supplied binary operator, and emits a single element stream.
export
foldChunks : p -> (p -> List o -> p) -> Stream f es o -> Stream f es p
foldChunks v g (S p) = S $ foldChunks v g p >>= output1

||| Folds all inputs using an initial value and binary operator
export %inline
fold : p -> (p -> o -> p) -> Stream f es o -> Stream f es p
fold v = foldChunks v . foldl

||| Folds all inputs using the supplied binary operator,
||| and emits a single-element stream, or the empty stream if
||| the input is empty, or the never stream if the input is non-terminating.
export
fold1 : (o -> o -> o) -> Stream f es o -> Stream f es o
fold1 g (S p) = S $ fold1 g p >>= maybe (pure ()) output1

export
foldMap : Monoid p => (o -> p) -> Stream f es o -> Stream f es p
foldMap g = foldChunks neutral (\v,vs => v <+> foldMap g vs)

export
concat : Monoid p => Stream f es p -> Stream f es p
concat = foldChunks neutral (\v,vs => v <+> concat vs)

||| Emits `False` and halts as soon as a non-matching
||| element is received; or emits a single `True` value if it
||| reaches the stream end and every input before that matches the predicate;
||| or hangs without emitting values if the input is
||| infinite and all inputs match the predicate.
export
all : (o -> Bool) -> Stream f es o -> Stream f es Bool
all pred (S p) = S $ all pred p >>= output1

||| Emits `Talse` and halts as soon as a non-matching
||| element is received; or emits a single `False` value if it
||| reaches the stream end and every input before that did not match
||| the predicate; or hangs without emitting values if the input is
||| infinite and all inputs do not match the predicate.
export
any : (o -> Bool) -> Stream f es o -> Stream f es Bool
any pred (S p) = S $ any pred p >>= output1

--------------------------------------------------------------------------------
-- Effects
--------------------------------------------------------------------------------

export %inline
drain : Stream f es o -> Stream f es q
drain = (>>= neutral)

export
observe : (o -> f es ()) -> Stream f es o -> Stream f es o
observe act stream = stream >>= \v => eval (act v) $> v

export %inline
resource : (acquire : f es r) -> (release : r -> f [] ()) -> Stream f es r
resource acq release =
  S $ Eval acq >>= \res => OScope (output1 res) (Just $ release res)

--------------------------------------------------------------------------------
-- Evaluating Streams
--------------------------------------------------------------------------------

parameters {0 f       : List Type -> Type -> Type}
           {auto merr : ELift1 s f}

  ||| Chunk-wise accumulates the values emitted by a stream.
  export covering %inline
  accumChunks : (init : a) -> (acc : a -> List o -> a) -> Stream f es o -> f es a
  accumChunks init acc = run . foldChunks init acc . pull

  ||| Accumulates the values emitted by a stream.
  export covering %inline
  accum : (init : a) -> (acc : a -> o -> a) -> Stream f es o -> f es a
  accum init acc = run . fold init acc . pull

  ||| Accumulates the values emitted by a stream in a snoclist.
  export covering %inline
  toSnoc : Stream f es o -> f es (SnocList o)
  toSnoc = accumChunks [<] (<><)

  ||| Accumulates the values emitted by a stream in a list.
  export covering %inline
  toList : Stream f es o -> f es (List o)
  toList = map (<>> []) . toSnoc

  ||| Accumulates the values emitted by a stream in a list.
  export covering %inline
  toChunks : Stream f es o -> f es (List $ List o)
  toChunks = map (<>> []) . accumChunks [<] (:<)

  ||| Runs a stream to completion, discarding all values it emits.
  export covering %inline
  run : Stream f es () -> f es ()
  run = accumChunks () (\_,_ => ())
