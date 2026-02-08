module FS.Concurrent.Signal

import Data.Linear.Deferred
import Data.Linear.Ref1
import Data.Linear.Traverse1
import Data.List.Quantifiers.Extra

import FS.Pull

import IO.Async

%default total

--------------------------------------------------------------------------------
-- Sinks
--------------------------------------------------------------------------------

public export
record Sink a where
  [noHints]
  constructor S
  sink1 : a -> IO1 ()

export
Semigroup (Sink a) where
  S s1 <+> S s2 = S $ \v,t => let _ # t := s1 v t in s2 v t

export
Monoid (Sink a) where
  neutral = S $ \_,t => () # t

export %inline
cmap : (b -> a) -> Sink a -> Sink b
cmap f (S g) = S (g . f)

export %inline
sink : HasIO io => (s : Sink a) => a -> io ()
sink = runIO . s.sink1

export %inline
sinkAs : HasIO io => (0 a : Type) -> (s : Sink a) => a -> io ()
sinkAs a = sink

--------------------------------------------------------------------------------
-- Signals
--------------------------------------------------------------------------------

record ST a where
  constructor SS
  value     : a
  last      : Nat
  listeners : List (Once World (a,Nat))

%inline
putImpl : a -> ST a -> (ST a, IO1 ())
putImpl v (SS _ lst []) = (SS v (S lst) [], (() # ))
putImpl v (SS _ lst ls) =
  let n := S lst
   in (SS v n [], traverse1_ (\o => putOnce1 o (v,n)) ls)

%inline
updImpl : (a -> (a,b)) -> ST a -> (ST a, IO1 b)
updImpl f (SS cur lst ls) =
  let n     := S lst
      (v,r) := f cur
   in ( SS v n []
      , \t => let _ # t := traverse1_ (\o => putOnce1 o (v,n)) ls t in r # t
      )

%inline
nextImpl :
     Poll (Async e)
  -> Nat
  -> Once World (a,Nat)
  -> ST a
  -> (ST a, Async e es (a,Nat))
nextImpl poll last once st@(SS v lst ls) =
  case last == lst of
    False => (st, pure (v,lst))
    True  => (SS v lst (once :: ls), poll (awaitOnce once))

export
record SignalRef a where
  [noHints]
  constructor SR
  ref : Ref World (ST a)

||| An observable, mutable value
export
signal : Lift1 World f => a -> f (SignalRef a)
signal v = SR <$> newref (SS v 1 [])

||| An observable, mutable reference that initially holds no value.
export %inline
emptySignal : Lift1 World f => (0 a : Type) -> f (SignalRef $ Maybe a)
emptySignal _ = signal Nothing

||| Reads the current value of the signal.
export %inline
get : Lift1 World f => SignalRef a -> f a
get (SR ref) = value <$> readref ref

||| Writes the current value to the signal.
export
put1 : SignalRef a -> (v : a) -> IO1 ()
put1 (SR ref) v t =
 let act # t := casupdate1 ref (putImpl v) t
  in act t

||| Lifted version of `put1`.
export %inline
put : Lift1 World f => SignalRef a -> (v : a) -> f ()
put r = lift1 . put1 r

||| Updates the value stored in the signal with the given function
||| and returns the second result of the computation.
export
update1 : SignalRef a -> (g : a -> (a,b)) -> IO1 b
update1 (SR ref) g t =
 let act # t := casupdate1 ref (updImpl g) t
  in act t

||| Lifted version of `update1`.
export %inline
update : Lift1 World f => SignalRef a -> (g : a -> (a,b)) -> f b
update r = lift1 . update1 r

||| Updates the value stored in the signal.
export %inline
modify1 : SignalRef a -> (g : a -> a) -> IO1 ()
modify1 s g = update1 s (\v => (g v, ()))

||| Lifted version of `modify1`.
export %inline
modify : Lift1 World f => SignalRef a -> (g : a -> a) -> f ()
modify r = lift1 . modify1 r

||| Updates the value stored in the signal and returns the result.
export %inline
updateAndGet1 : SignalRef a -> (g : a -> a) -> IO1 a
updateAndGet1 s g = update1 s (\v => let w := g v in (w,w))

||| Lifted version of `updateAndGet1`.
export %inline
updateAndGet : Lift1 World f => SignalRef a -> (g : a -> a) -> f a
updateAndGet r = lift1 . updateAndGet1 r

||| Awaits the next value and its count, potentially blocking the
||| current fiber if the internal counter is at `current`.
|||
||| Note: The internal counter starts at `1`, so invoking this with
|||       a count of `0` will always immediately return the internal
|||       value and count.
export
next : SignalRef a -> Nat -> Async e es (a,Nat)
next (SR ref) n = do
  def <- onceOf (a,Nat)
  uncancelable $ \poll => do
    act <- update ref (nextImpl poll n def)
    act

export %hint
signalSink : (r : SignalRef t) => Sink t
signalSink = S (put1 r)

export %hint
emptySignalSink : (r : SignalRef (Maybe t)) => Sink t
emptySignalSink = S (put1 r . Just)

--------------------------------------------------------------------------------
-- Signal Streams
--------------------------------------------------------------------------------

||| An observe-only wrapper around a `SignalRef`.
|||
||| Use this if you still want to observe a mutable value by means of
||| `discrete` or `continuous` but you want to prevent it to be further used
||| as a data sink.
export
record Signal a where
  [noHints]
  constructor SI
  sref : SignalRef a

export %inline %hint
ref2sig : SignalRef a => Signal a
ref2sig @{r} = SI r

export %inline
sig : SignalRef a -> Signal a
sig = SI

public export
interface Reference (0 t : Type -> Type) where
  current1 : t a -> IO1 a

export %inline
current : LIO f => Reference t => t a -> f a
current = lift1 . current1

||| Creates a continuous stream of values typically by reading
||| the current state of a mutable reference every time a value is
||| pulled.
export
continuous : LIO (f es) => Reference t => t a -> Stream f es a
continuous = repeat . eval . current

export %inline
Reference IORef where
  current1 = read1

export %inline
Reference SignalRef where
  current1 = ioToF1 . get

export %inline
Reference Signal where
  current1 = current1 . sref

public export
interface Discrete (0 t : Type -> Type) where
  ||| Creates a discrete stream of values that reads an observable
  ||| value every time it changes.
  |||
  ||| Note: There is no buffering of values. If the signal is updated
  |||       more quickly than the stream is being pulled, some values
  |||       might be lost.
  discrete : t a -> Stream (Async e) es a

export
Discrete SignalRef where
  discrete s = unfoldEval 0 (map (uncurry More) . next s)

export %inline
Discrete Signal where
  discrete = discrete . sref

||| Like `discrete` but for an initially empty signal.
|||
||| Fires whenever a `Just` is put into the signal.
export %inline
justs : Discrete t => t (Maybe a) -> Stream (Async e) es a
justs s = discrete s |> catMaybes

||| Blocks the fiber and observes the given signal until the given
||| predicate returns `True`.
export
until : Discrete f => f a -> (a -> Bool) -> Async e [] ()
until ref pred = assert_total $ discrete ref |> any pred |> drain |> mpull

--------------------------------------------------------------------------------
-- Writing from Streams to Signals
--------------------------------------------------------------------------------

parameters {0 f      : List Type -> Type -> Type}
           {0 es     : List Type}
           {0 p,r    : Type}
           {auto lio : LIO (f es)}
           (sig      : SignalRef p)

  ||| Use the output of a pull to update the value in a signal.
  export
  modSig : (o -> p -> p) -> Pull f o es r -> Pull f o es r
  modSig f = observe (modify sig . f)

  ||| Use the output of a pull to update the value in a signal.
  export
  setSig : Pull f p es r -> Pull f p es r
  setSig = observe (put sig)

  ||| Act on the output of a pull by combining it with the current
  ||| value in a signal.
  export
  observeSig : (o -> p -> f es ()) -> Pull f o es r -> Pull f o es r
  observeSig f = observe $ \vo => get sig >>= f vo

  ||| Like `observeSig` but drains the stream in the process.
  export
  foreachSig : (o -> p -> f es ()) -> Pull f o es r -> Pull f q es r
  foreachSig f = foreach $ \vo => get sig >>= f vo

||| Generalization of `observeSig`: Acts on the output of a pull by combining
||| with the values from a heterogeneous list of signals.
export
hobserveSig :
     {0 f      : List Type -> Type -> Type}
  -> {0 es,ts  : List Type}
  -> {auto lio : LIO (f es)}
  -> All Signal ts
  -> HZipFun (o::ts) (f es ())
  -> Pull f o es r
  -> Pull f o es r
hobserveSig sigs fun =
  observe $ \vo => Prelude.do
    vs <- hsequence $ mapProperty current sigs
    happly fun (vo::vs)

||| Like `hobserveSig` but drains the stream in the process.
export
hforeachSig :
     {0 f      : List Type -> Type -> Type}
  -> {0 es,ts  : List Type}
  -> {auto lio : LIO (f es)}
  -> All Signal ts
  -> HZipFun (o::ts) (f es ())
  -> Pull f o es r
  -> Pull f q es r
hforeachSig sigs fun =
  foreach $ \vo => Prelude.do
    vs <- hsequence $ mapProperty current sigs
    happly fun (vo::vs)
