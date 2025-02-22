module Main

import Test.FS.Internal
import Test.FS.Pull
import Test.FS.Stream
import Test.FS.Bytes

main : IO ()
main =
  test
    [ Internal.props
    , Pull.props
    , Stream.props
    , Bytes.props
    ]
