module Main

import Test.FS.Internal
import Test.FS.Pull
import Test.FS.Bytes

main : IO ()
main =
  test
    [ Internal.props
    , Pull.props
    , Bytes.props
    ]
