module Main

import IO.Async.Loop.Sync
import Test.FS.Bytes
import Test.FS.Internal
import Test.FS.Pull
import Test.FS.Resource

main : IO ()
main = do
  sy <- sync
  runAsync sy $ runTree $
    Node "Pull Spec"
      [ Resource.specs
      ]
  test
    [ Internal.props
    , Pull.props
    , Bytes.props
    ]
