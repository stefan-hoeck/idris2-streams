module Main

import Test.FS.Internal
import Test.FS.Pull
import Test.FS.Stream

main : IO ()
main =
  test
    [ Internal.props
    , Pull.props
    , Stream.props
    ]
