module FS.Resource

import public Control.Monad.MCancel
import public Control.Monad.Resource
import public FS.Pull

%default total

||| Acquires a resource that will be released once the current
||| scope is cleaned up.
export %inline
acquire : (acq : f es r) -> (release : r -> f [] ()) -> Pull f o es r
acquire = Acquire

||| Like `bracket`, but acquires the resource in the current scope.
export
bracketWeak : (f es x) -> (x -> f [] ()) -> (x -> Pull f o es r) -> Pull f o es r
bracketWeak acq cleanup g = acquire acq cleanup >>= g

||| Acquires a resource used for running a stream
||| making sure it is properly cleaned up once the stream terminates.
export %inline
bracket : (f es x) -> (x -> f [] ()) -> (x -> Pull f o es r) -> Pull f o es r
bracket acq cl = newScope . bracketWeak acq cl

||| Makes sure the given cleanup action is run once the stream
||| terminates.
|||
||| Like `finally` but does not create a new inner scope.
export
finallyWeak : Applicative (f es) => f [] () -> Pull f o es r -> Pull f o es r
finallyWeak cleanup = bracketWeak (pure ()) (const cleanup) . const

||| Makes sure the given cleanup action is run once the stream
||| terminates.
export
finally : Applicative (f es) => f [] () -> Pull f o es r -> Pull f o es r
finally cleanup = bracket (pure ()) (const cleanup) . const

||| Like `resource`, but acquires the resource in the current scope.
export %inline
resourceWeak :
     {auto res : Resource f x}
  -> (acquire : f es x)
  -> (x -> Pull f o es r)
  -> Pull f o es r
resourceWeak acq = bracketWeak acq cleanup

||| Acquires a resource in a new scope, closing it once the scope is
||| cleaned up.
export %inline
resource :
     {auto res : Resource f x}
  -> (acquire : f es x)
  -> (x -> Pull f o es r)
  -> Pull f o es r
resource acq = bracket acq cleanup

export
resourcesWeak :
     {auto all : All (Resource f) rs}
  -> (acquire : All (f es) rs)
  -> (HList rs -> Pull f o es r)
  -> Pull f o es r
resourcesWeak @{_ :: _} (a::as) g =
  resourceWeak a $ \r => resourcesWeak as (\res => g (r::res))
resourcesWeak @{[]} [] g = g []

export
resources :
     {auto all : All (Resource f) rs}
  -> (acquire : All (f es) rs)
  -> (HList rs -> Pull f o es r)
  -> Pull f o es r
resources acqs = newScope . resourcesWeak acqs

||| Like `uncons`, but pairs the tail of the `Pull` with the `Scope`
||| it should be run in.
|||
||| Use this for evaluating several `Pull`s in parallel, for instance
||| when zipping or merging them. This will make sure that all resources
||| will be released in the correct order.
export
stepLeg : StepLeg f es o -> Pull f q es (Maybe (o, StepLeg f es o))
stepLeg (SL p sc) =
  inScope sc $ do
    uncons p >>= \case
      Left _       => pure Nothing
      Right (v,tl) => (\sc => Just (v, SL tl sc)) <$> scope

||| Utility for consing some values onto a pull and running it in
||| its desired scope.
export
endLeg : o -> StepLeg f es o -> Pull f o es ()
endLeg vs (SL p sc) = inScope sc (cons vs p)
