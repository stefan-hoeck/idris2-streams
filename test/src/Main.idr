module Main

import Test.FS.Internal
import Test.FS.Pull

main : IO ()
main =
  test
    [ Internal.props
    , Pull.props
    ]
