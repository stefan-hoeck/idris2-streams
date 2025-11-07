module FS.Resource

import public Control.Monad.MCancel
import public Control.Monad.Resource
import public FS.Pull

%default total

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
