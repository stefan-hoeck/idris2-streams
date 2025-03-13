module FS.Stream

import public Control.Monad.MCancel
import public Control.Monad.Resource
import public Data.Linear.ELift1
import public FS.Chunk
import public FS.Scope

import Data.Linear.Deferred
import Data.Linear.Ref1
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
  mapImpl f p  = S (mapOutput f p.pull)
  appImpl f p  = bind f (`mapImpl` p)

export %inline
Semigroup (Stream f es o) where
  S p <+> S q = S $ p >> q

export %inline
Monoid (Stream f es o) where
  neutral = S (pure ())

export %inline
ELift1 s f => ELift1 s (Stream f) where
  elift1 act = S (elift1 act >>= output1)

export %inline
ELift1 World f => HasIO (Stream f es) where
  liftIO act = lift1 (ioToF1 act)

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
emits : Chunk o -> Stream f es o
emits = S . output

||| Creates an empti stream that just evaluates the supplied effect.
||| If the effect fails, the returned stream fails.
export %inline
exec : f es () -> Stream f es o
exec = S . Eval

||| Creates a single element stream that gets its value by evaluating the
||| supplied effect. If the effect fails, the returned stream fails.
export %inline
eval : f es o -> Stream f es o
eval act = S (Eval act >>= output1)

||| Like `eval` but emits the result as a single chunk
export %inline
evals : f es (Chunk o) -> Stream f es o
evals act = S (Eval act >>= output)

||| Like `eval` but emits the result as a single chunk
export %inline
evalList : f es (List o) -> Stream f es o
evalList act = S (Eval act >>= outputList)

export %inline
evalFoldable : Foldable m => f es (m o) -> Stream f es o
evalFoldable act = S (Eval act >>= foldable)

||| Creates a stream by successively applying
||| the given generator function to the threaded state
||| until a `Nothing` is returned
export %inline
unfold1 : ChunkSize => (init : st) -> (st -> Maybe (o,st)) -> Stream f es o
unfold1 init g = S $ unfoldMaybe1 init g

||| Like `unfoldMaybe` but emits values in chunks.
export %inline
unfold : (init : st) -> (st -> (Chunk o, Maybe st)) -> Stream f es o
unfold init g = S $ unfoldMaybe init g

||| Generates a stream from the given list of chunks. Empty chunks
||| will be silently dropped.
export %inline
fromChunks : List (Chunk o) -> Stream f es o
fromChunks vss = S $ fromChunks vss

||| Produces values via the given effectful computations until it returns
||| `Nothing`.
export %inline
unfoldEval1 : f es (Maybe o) -> Stream f es o
unfoldEval1 act = S $ unfoldEvalMaybe1 act

||| Produces values via the given effect- and stateful computations
||| until it returns `Nothing`.
export %inline
unfoldEvalST1 : x -> (x -> f es (Maybe (o,x))) -> Stream f es o
unfoldEvalST1 st act = S $ unfoldEvalST1 st act

||| Produces chunks of values via the given effectful computations until
||| it returns `Nothing`.
export %inline
unfoldEval : f es (Maybe $ Chunk o) -> Stream f es o
unfoldEval act = S $ unfoldEvalMaybe act

||| Infinitely repeats the given stream.
export
repeat : Stream f es o -> Stream f es o
repeat (S v) = S $ repeat v

||| An infinite stream constantly emitting the given value
||| in chunks of the given size.
export %inline
constant : ChunkSize => o -> Stream f es o
constant v = S $ fill v

||| Turns an effectful stream generator into a regular stream.
export %inline
force : f es (Stream f es o) -> Stream f es o
force = join . eval

||| An infinite stream of values generated by repeatedly applying
||| the given function to a starting value.
|||
||| Generates chunks of the specified size.
export %inline
iterate : ChunkSize => o -> (o -> o) -> Stream f es o
iterate v f = S $ iterate v f

--------------------------------------------------------------------------------
-- Resource Management
--------------------------------------------------------------------------------

export %inline
stream : Pull f o es () -> Stream f es o
stream p = S (OScope None p)

export %inline
scope : Stream f es o -> Stream f es o
scope = stream . pull

export %inline
currentScope : Stream f es (Scope f)
currentScope = S (scope >>= output1)

--------------------------------------------------------------------------------
-- Combinators
--------------------------------------------------------------------------------
--
-- ||| Prepends a chunk of values to the front of a stream
-- export %inline
-- cons : List o -> Stream f es o -> Stream f es o
-- cons vs = S . cons vs . pull
--
-- ||| Prepends a single value to the front of a stream
-- export %inline
-- cons1 : o -> Stream f es o -> Stream f es o
-- cons1 = cons . pure
--
-- ||| Alias for `(<+>)`
-- export %inline
-- (++) : Stream f es o -> Stream f es o -> Stream f es o
-- (++) = (<+>)
--
-- ||| Emits the first `n` values of a stream
-- export %inline
-- take : Nat -> Stream f es o -> Stream f es o
-- take n = stream . ignore . take n . pull
--
-- export
-- replicate : ChunkSize => Nat -> o -> Stream f es o
-- replicate n v = S $ replicate n v
--
-- ||| Emits the last `n` values of a stream
-- |||
-- ||| Note: The whole `n` values have to be kept in memory, therefore,
-- |||       the result will be emitted as a single chunk. Take memory
-- |||       consumption into account when using this for very large `n`.
-- export
-- takeRight : (n : Nat) -> (0 p : IsSucc n) => Stream f es o -> Stream f es o
-- takeRight n (S p) = S $ takeRight n p >>= output
--
-- ||| Emits values until the given predicate returns `False`.
-- export
-- takeWhile : (o -> Bool) -> Stream f es o -> Stream f es o
-- takeWhile pred = stream . ignore . takeWhile pred . pull
--
-- ||| Like `takeWhile` but also includes the first failure.
-- export %inline
-- takeThrough : (o -> Bool) -> Stream f es o -> Stream f es o
-- takeThrough pred = stream . ignore . takeThrough pred . pull
--
||| Emits values until the first `Nothing` is encountered.
export
takeWhileJust : Stream f es (Maybe o) -> Stream f es o
takeWhileJust = stream . ignore . takeWhileJust . pull
--
-- ||| Drops `n` elements of the input, then echoes the rest.
-- export
-- drop : Nat -> Stream f es o -> Stream f es o
-- drop n (S p) = S $ drop n p >>= fromMaybe (pure ())
--
-- ||| Only keeps the first element of the input.
-- export %inline
-- head : Stream f es o -> Stream f es o
-- head = take 1
--
-- ||| Drops the first element of the input.
-- export %inline
-- tail : Stream f es o -> Stream f es o
-- tail = drop 1
--
-- ||| Drops values from a stream while the given predicate returns `True`,
-- ||| then echoes the rest.
-- export
-- dropWhile : (o -> Bool) -> Stream f es o -> Stream f es o
-- dropWhile pred (S p) = S $ dropWhile pred p >>= fromMaybe (pure ())
--
-- ||| Like `dropWhile` but also drops the first value where
-- ||| the predicate returns `False`.
-- export
-- dropThrough : (o -> Bool) -> Stream f es o -> Stream f es o
-- dropThrough pred (S p) = S $ dropThrough pred p >>= fromMaybe (pure ())

||| Emits the first value fulfilling the given predicate.
export
find : (o -> Bool) -> Stream f es o -> Stream f es o
find pred (S p) =
  stream $ do
    Just (v,_) <- find pred p | Nothing => pure ()
    output1 v

||| Chunk-wise maps the values produced by a stream
export %inline
mapChunk : (Chunk o -> Chunk p) -> Stream f es o -> Stream f es p
mapChunk f = S . mapChunk f . pull

||| Chunk-wise maps the values produced by a stream
export %inline
mapChunkEval : (Chunk o -> f es (Chunk p)) -> Stream f es o -> Stream f es p
mapChunkEval f = S . mapChunkEval f . pull

||| Chunk-wise consumes the output, draining the given stream.
export %inline
sinkChunk : (Chunk o -> f es ()) -> Stream f es o -> Stream f es p
sinkChunk f = S . sinkChunk f . pull

||| Consumes the output one value at a time, draining the given stream.
|||
||| See also `sinkChunk` for a potentially more efficient version.
export %inline
sink : (o -> f es ()) -> Stream f es o -> Stream f es p
sink f = S . sink f . pull

||| Emits only inputs which match the supplied predicate.
export %inline
filter : (o -> Bool) -> Stream f es o -> Stream f es o
filter pred = S . filter pred . pull

||| Emits only inputs which do not match the supplied predicate.
export %inline
filterNot : (o -> Bool) -> Stream f es o -> Stream f es o
filterNot pred = filter (not . pred)

||| Emits only inputs for which the given function returns a `Just`
export %inline
mapMaybe : (o -> Maybe p) -> Stream f es o -> Stream f es p
mapMaybe = mapChunk . mapMaybe

||| Emits the chunks of the input stream.
export %inline
chunks : Stream f es o -> Stream f es (Chunk o)
chunks = mapChunk singleton

||| Alias for `s >>= eval . f`
export %inline
evalMap : (o -> f es p) -> Stream f es o -> Stream f es p
evalMap f s = s >>= eval . f

||| Like `evalMap`, but operates on chunks for performance.
export
evalMapChunk : (Chunk o -> f es (Chunk p)) -> Stream f es o -> Stream f es p
evalMapChunk g s = chunks s >>= evals . g

||| Chunk-wise folds all inputs using an initial
||| value and supplied binary operator, and emits a single element stream.
export
foldChunk : p -> (p -> Chunk o -> p) -> Stream f es o -> Stream f es p
foldChunk v g (S p) = S $ foldChunk v g p >>= output1

||| Folds all inputs using an initial value and binary operator
export %inline
fold : p -> (p -> o -> p) -> Stream f es o -> Stream f es p
fold v = foldChunk v . foldl

||| Accumulates all values in a stream as their sum.
export %inline
sum : Num o => Stream f es o -> Stream f es o
sum = fold 0 (+)

||| Accumulates all values in a stream as their product.
export %inline
product : Num o => Stream f es o -> Stream f es o
product = fold 1 (*)

||| Maps and accumulates the values in a stream via a `Monoid`.
|||
||| Note: Unlike `appendMap`, this will always result in single-element stream
export
foldMap : Monoid p => (o -> p) -> Stream f es o -> Stream f es p
foldMap g = foldChunk neutral (\v,vs => v <+> foldMap g vs)

||| Accumulates the values in a stream via a `Monoid`.
|||
||| Note: Unlike `append`, this will always result in single-element stream
export
concat : Monoid p => Stream f es p -> Stream f es p
concat = foldChunk neutral (\v,vs => v <+> concat vs)

||| Folds all inputs using the supplied binary operator,
||| emitting a single-element stream, or the empty stream if
||| the input is empty, or the never stream if the input is non-terminating.
export
fold1 : (o -> o -> o) -> Stream f es o -> Stream f es o
-- fold1 g (S p) = S $ fold1 g p >>= maybe (pure ()) output1

||| Emits the largest value found in a stream.
export %inline
maximum : Ord o => Stream f es o -> Stream f es o
maximum = fold1 max

||| Emits the smallest value found in a stream.
export %inline
minimum : Ord o => Stream f es o -> Stream f es o
minimum = fold1 min

||| Emits the number of values encountered
export %inline
count : Stream f es o -> Stream f es Nat
count = fold 0 (const . S)
--
-- ||| Maps and accumulates the values in a stream via a `Semigroup`.
-- |||
-- ||| Note: Unlike `concat`, this will return an empty stream if the input
-- |||       is empty.
-- export %inline
-- append : Semigroup o => Stream f es o -> Stream f es o
-- append = fold1 (<+>)

-- ||| Maps and accumulates the values in a stream via a `Semigroup`.
-- |||
-- ||| Note: Unlike `foldMap`, this will return an empty stream if the input
-- |||       is empty.
-- export %inline
-- appendMap : Semigroup p => (o -> p) -> Stream f es o -> Stream f es p
-- appendMap f = append . map f

||| Emits `False` and halts as soon as a non-matching
||| element is received; or emits a single `True` value if it
||| reaches the stream end and every input before that matches the predicate;
||| or hangs without emitting values if the input is
||| infinite and all inputs match the predicate.
export
all : (o -> Bool) -> Stream f es o -> Stream f es Bool
all pred (S p) = stream $ all pred p >>= output1

||| Emits `Talse` and halts as soon as a non-matching
||| element is received; or emits a single `False` value if it
||| reaches the stream end and every input before that did not match
||| the predicate; or hangs without emitting values if the input is
||| infinite and all inputs do not match the predicate.
export
any : (o -> Bool) -> Stream f es o -> Stream f es Bool
any pred (S p) = stream $ any pred p >>= output1

||| Wraps the values emitted by this stream in a `Just` and
||| marks its end with a `Nothing`.
export
endWithNothing : Stream f es o -> Stream f es (Maybe o)
endWithNothing s = map Just s <+> pure Nothing

--------------------------------------------------------------------------------
-- Scans
--------------------------------------------------------------------------------
--
-- ||| General stateful conversion of a `Streams`s output.
-- |||
-- ||| Aborts as soon as the given accumulator function returns `Nothing`
-- export
-- scanChunksMaybe :
--      st
--   -> (st -> Maybe (List o -> (List p,st)))
--   -> Stream f es o
--   -> Stream f es p
-- scanChunksMaybe s1 f = stream . ignore . scanChunksMaybe s1 f . pull
--
-- ||| Threads a stateful computation through all the chunks emitted by
-- ||| a stream, generating a final (possibly empty) chunk of values when
-- ||| the stream is exhausted.
-- export %inline
-- scanChunksFull :
--      (init : st)
--   -> (fun  : st -> List o -> (List p,st))
--   -> (end  : st -> List p)
--   -> Stream f es o
--   -> Stream f es p
-- scanChunksFull init fun end (S pl) =
--   S $ scanChunks init fun pl >>= output . end
--
-- ||| Like `scanChunksMaybe` but will transform the whole output.
-- export %inline
-- scanChunks :
--      (init: st)
--   -> (st -> List o -> (List p,st))
--   -> Stream f es o
--   -> Stream f es p
-- scanChunks init fun = S . ignore . scanChunks init fun . pull
--
-- export %inline
-- mapAccumulate :
--      (init: st)
--   -> (st -> o -> (st,p))
--   -> Stream f es o
--   -> Stream f es p
-- mapAccumulate init fun = scanChunks init (mapAccum [<] fun)
--
-- ||| Zips the input with a running total according to `s`, up to but
-- ||| not including the current element. Thus the initial
-- ||| `vp` value is the first emitted to the output:
-- export
-- zipWithScan : p -> (p -> o -> p) -> Stream f es o -> Stream f es (o,p)
-- zipWithScan vp fun =
--   mapAccumulate vp $ \vp1,vo =>
--     let vp2 := fun vp1 vo
--      in (vp2, (vo, vp1))
--
-- ||| Pairs each element in the stream with its 0-based index.
-- export %inline
-- zipWithIndex : Stream f es o -> Stream f es (o,Nat)
-- zipWithIndex = zipWithScan 0 (\n,_ => S n)
--
-- ||| Like `zipWithScan` but the running total is including the current element.
-- export
-- zipWithScan1 : p -> (p -> o -> p) -> Stream f es o -> Stream f es (o,p)
-- zipWithScan1 vp fun =
--   mapAccumulate vp $ \vp1,vo =>
--     let vp2 := fun vp1 vo
--      in (vp2, (vo, vp2))
--
-- ||| Zips each element of this stream with the previous element wrapped into `Some`.
-- ||| The first element is zipped with `None`.
-- export %inline
-- zipWithPrevious : Stream f es o -> Stream f es (Maybe o, o)
-- zipWithPrevious = mapAccumulate Nothing $ \m,vo => (Just vo, (m, vo))
--
--
-- ||| Emits the given separator between every pair of elements in the
-- ||| source stream.
-- export
-- intersperse : (sep : o) -> Stream f es o -> Stream f es o
-- intersperse sep (S p) =
--   S $ uncons1 p >>= \case
--     Left _      => pure ()
--     Right (h,t) => cons [h] (mapChunks (>>= \v => [sep,v]) t)
--
-- ||| Similar to `fold` but emits the currently accumulated state
-- ||| on every output.
-- export
-- scan : p -> (p -> o -> p) -> Stream f es o -> Stream f es p
-- scan ini f = mapAccumulate ini (\t,v => let next := f t v in (next,next))
--
-- ||| Emits a running total of the values emitted.
-- export %inline
-- runningTotal : Num o => Stream f es o -> Stream f es o
-- runningTotal = scan 0 (+)
--
-- ||| Emits a running count (starting at 1) of the number of values emitted.
-- export %inline
-- runningCount : Stream f es o -> Stream f es Nat
-- runningCount = scan 0 (const . S)
--
-- --------------------------------------------------------------------------------
-- -- Zipping Streams
-- --------------------------------------------------------------------------------
--
-- 0 ZipWithLeft : (List Type -> Type -> Type) -> List Type -> (i,o : Type) -> Type
-- ZipWithLeft f es i o = List i -> Pull f i es () -> Pull f o es ()
--
-- %inline
-- adjLeg : (Pull f o es () -> Pull f p es ()) -> StepLeg f es o -> Pull f p es ()
-- adjLeg f (SL p sc) = inScope sc (f p)
--
-- zipWithImpl :
--      ZipWithLeft f es o q
--   -> ZipWithLeft f es p q
--   -> (o -> p -> q)
--   -> Stream f es o
--   -> Stream f es p
--   -> Stream f es q
-- zipWithImpl k1 k2 fun (S os) (S ps) =
--   stream $ Prelude.do
--     sc           <- scope
--     Just (h1,t1) <- stepLeg (SL os sc) | Nothing => inScope sc (k2 [] ps)
--     Just (h2,t2) <- stepLeg (SL ps sc) | Nothing => adjLeg (k1 h1) t1
--     go h1 h2 t1 t2
--
--   where
--     go : List o -> List p -> StepLeg f es o -> StepLeg f es p -> Pull f q es ()
--     go h1 h2 t1 t2 =
--       assert_total $ case zipImpl [<] fun h1 h2 of
--         Z cs => do
--           output cs
--           Just (h3,t3) <- stepLeg t1 | Nothing => adjLeg (k2 []) t2
--           Just (h4,t4) <- stepLeg t2 | Nothing => adjLeg (k1 h3) t3
--           go h3 h4 t3 t4
--         ZL os cs => do
--           output cs
--           Just (h4,t4) <- stepLeg t2 | Nothing => adjLeg (k1 os) t1
--           go os h4 t1 t4
--         ZR ps cs => do
--           output cs
--           Just (h3,t3) <- stepLeg t1 | Nothing => adjLeg (k2 ps) t2
--           go h3 ps t3 t2
--
-- ||| Zips the elements of two streams, combining them via the given binary
-- ||| function.
-- |||
-- ||| This terminates when the end of either branch is reached.
-- export %inline
-- zipWith : (o -> p -> q) -> Stream f es o -> Stream f es p -> Stream f es q
-- zipWith = zipWithImpl (\_,_ => pure ()) (\_,_ => pure ())
--
-- ||| Convenience alias for `zipWith MkPair`
-- export %inline
-- zip : Stream f es o -> Stream f es p -> Stream f es (o,p)
-- zip = zipWith MkPair
--
-- ||| Determinsitically zips elements with the specified function, terminating
-- ||| when the ends of both branches are reached naturally, padding the left
-- ||| branch with `pad1` and padding the right branch with `pad2` as necessary.
-- export %inline
-- zipAllWith :
--      (pad1 : o)
--   -> (pad2 : p)
--   -> (fund : o -> p -> q)
--   -> Stream f es o
--   -> Stream f es p
--   -> Stream f es q
-- zipAllWith vo vp fun =
--   zipWithImpl
--     (\ho,to => output (flip fun vp <$> ho) >> mapOutput (flip fun vp) to)
--     (\hp,tp => output (fun vo <$> hp) >> mapOutput (fun vo) tp)
--     fun
--
-- ||| Determinsitically zips elements, terminating when the ends of both branches
-- ||| are reached naturally, padding the left or right branch
-- ||| as necessary.
-- export %inline
-- zipAll : o -> p -> Stream f es o -> Stream f es p -> Stream f es (o,p)
-- zipAll vo vp = zipAllWith vo vp MkPair
--
-- ||| Deterministically interleaves elements, starting on the left,
-- ||| terminating when the end of either branch is reached naturally.
-- export %inline
-- interleave : Stream f es o -> Stream f es o -> Stream f es o
-- interleave xs ys = zip xs ys >>= \(x,y) => emits [x,y]
--
-- ||| Deterministically interleaves elements, starting on the left,
-- ||| terminating when the ends of both branches are reached naturally.
-- export
-- interleaveAll : Stream f es o -> Stream f es o -> Stream f es o
-- interleaveAll xs ys =
--   zipAll [] [] (map pure xs) (map pure ys) >>= \(l,r) => emits (l ++ r)

--------------------------------------------------------------------------------
-- Observing and Draining Streams
--------------------------------------------------------------------------------

||| Performs the given action on each emitted value, thus draining
||| the stream, consuming all its output.
export %inline
foreach1 : (o -> f es ()) -> Stream f es o -> Stream f es q
foreach1 f = (>>= exec . f)

||| Perform the given action on every chunk of output thus draining
||| the stream, consuming all its output.
|||
||| For acting on values without actually draining the stream, see
||| `observe` and `observeChunk`.
export %inline
foreach : (Chunk o -> f es ()) -> Stream f es o -> Stream f es q
foreach f = foreach1 f . chunks

||| Empties a stream silently dropping all output.
export %inline
drain : Stream f es o -> Stream f es q
drain = mapChunk (const neutral)

||| Performs the given action on every value of the stream without
||| otherwise affecting the emitted values.
export
observe1 : (o -> f es ()) -> Stream f es o -> Stream f es o
observe1 act stream = stream >>= \v => eval (act v) $> v

||| Performs the given action on every chunk of values without
||| otherwise affecting the emitted values.
export
observe : (Chunk o -> f es ()) -> Stream f es o -> Stream f es o
observe act stream =
  chunks stream >>= \vs => eval (act vs) >> emits vs

--------------------------------------------------------------------------------
-- Resource Management
--------------------------------------------------------------------------------

||| Like `bracket`, but acquires the resource in the current scope.
export
bracketWeak :
     (f es r)
  -> (r -> f [] ())
  -> (r -> Stream f es o)
  -> Stream f es o
bracketWeak acq cleanup g = S (acquire acq cleanup >>= pull . g)

||| Acquires a resource used for running a stream
||| making sure it is properly cleaned up once the stream terminates.
export %inline
bracket :
     (f es r)
  -> (r -> f [] ())
  -> (r -> Stream f es o)
  -> Stream f es o
bracket acq cl = stream . pull . bracketWeak acq cl

||| Makes sure the given cleanup action is run once the stream
||| terminates.
|||
||| Like `finally` but does not create a new inner scope.
export
finallyWeak : Applicative (f es) => f [] () -> Stream f es o -> Stream f es o
finallyWeak cleanup = bracketWeak (pure ()) (const cleanup) . const

||| Makes sure the given cleanup action is run once the stream
||| terminates.
export
finally : Applicative (f es) => f [] () -> Stream f es o -> Stream f es o
finally cleanup = bracket (pure ()) (const cleanup) . const

||| Like `resource`, but acquires the resource in the current scope.
export %inline
resourceWeak :
     {auto res : Resource f r}
  -> (acquire : f es r)
  -> (r -> Stream f es o)
  -> Stream f es o
resourceWeak acq = bracketWeak acq cleanup

||| Acquires a resource in a new scope, closing it once the scope is
||| cleaned up.
export %inline
resource :
     {auto res : Resource f r}
  -> (acquire : f es r)
  -> (r -> Stream f es o)
  -> Stream f es o
resource acq = bracket acq cleanup

export
resourcesWeak :
     {auto all : All (Resource f) rs}
  -> (acquire : All (f es) rs)
  -> (HList rs -> Stream f es o)
  -> Stream f es o
resourcesWeak @{_ :: _} (a::as) g =
  resourceWeak a $ \r => resourcesWeak as (\res => g (r::res))
resourcesWeak @{[]} [] g = g []

export
resources :
     {auto all : All (Resource f) rs}
  -> (acquire : All (f es) rs)
  -> (HList rs -> Stream f es o)
  -> Stream f es o
resources acqs = stream . pull . resourcesWeak acqs

--------------------------------------------------------------------------------
-- Evaluating Streams
--------------------------------------------------------------------------------

parameters {0 f       : List Type -> Type -> Type}
           {auto tgt  : Target s f}
           {auto mcnc : MCancel f}

  ||| Chunk-wise accumulates the values emitted by a stream.
  export covering
  accumChunk : (ini : a) -> (acc : a -> Chunk o -> a) -> Stream f es o -> f es a
  accumChunk init acc (S p) =
    weakenErrors (run (foldChunk init acc p)) >>= \case
      Succeeded v => pure v
      Error x     => fail x
      Canceled    => pure init

  ||| Accumulates the values emitted by a stream.
  export covering %inline
  accum : (init : a) -> (acc : a -> o -> a) -> Stream f es o -> f es a
  accum init acc = accumChunk init (foldl acc)

  ||| Accumulates the values emitted by a stream in a snoclist.
  export covering %inline
  toSnoc : Stream f es o -> f es (SnocList o)
  toSnoc = accumChunk [<] (\sc,c => sc <>< toList c)

  ||| Accumulates the values emitted by a stream in a list.
  export covering %inline
  toList : Stream f es o -> f es (List o)
  toList = map (<>> []) . toSnoc

  ||| Accumulates the values emitted by a stream in a list.
  export covering %inline
  toChunks : Stream f es o -> f es (List $ Chunk o)
  toChunks = map (<>> []) . accumChunk [<] (:<)

  ||| Runs a stream to completion, discarding all values it emits.
  export covering %inline
  run : Stream f es Void -> f es ()
  run = accumChunk () (\_,_ => ())
