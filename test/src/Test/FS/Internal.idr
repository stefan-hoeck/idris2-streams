module Test.FS.Internal

import Data.Chunk
import FS.Pull
import Test.FS.Util

%default total

init : List a -> List a
init []     = []
init [v]    = []
init (h::t) = h :: init t

-- prop_chunkedConcat : Property
-- prop_chunkedConcat =
--   property $ do
--     [CS sz,vs] <- forAll $ hlist [chunkSizes, list (linear 0 30) bytes]
--     fastConcat (chunked sz vs) === chunkL vs

-- prop_chunkedSize : Property
-- prop_chunkedSize =
--   property $ do
--     [CS sz,vs] <- forAll $ hlist [chunkSizes, byteLists]
--     assert (all ((sz ==) . length) (init $ chunked sz vs))

-- prop_chunkedSizeLTE : Property
-- prop_chunkedSizeLTE =
--   property $ do
--     [CS sz,vs] <- forAll $ hlist [chunkSizes, byteLists]
--     assert (all ((sz >=) . length) (chunked sz vs))

export
props : Group
props =
  MkGroup "FS.Internal.Chunk"
    [ -- ("prop_chunkedConcat", prop_chunkedConcat)
--     , ("prop_chunkedSize", prop_chunkedSize)
--     , ("prop_chunkedSizeLTE", prop_chunkedSizeLTE)
    ]
