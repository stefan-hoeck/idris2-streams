module Main

import IO.Async.Loop.Sync
import Test.FS.Bracket
import Test.FS.Bytes
import Test.FS.Concurrent
import Test.FS.Internal
import Test.FS.Pull
import Test.FS.Resource

main : IO ()
main = do
  sy <- sync
  runAsync sy $ runTree $
    Node "Pull Spec"
      [ Concurrent.specs
      , Resource.specs
      , Bracket.specs
      ]
  test
    [ Internal.props
    , Pull.props
    , Bytes.props
    ]
