module Test.FS.Bytes

import Control.Monad.Elin
import Data.Buffer.Indexed
import Data.ByteString
import Data.ByteVect
import Data.String
import FS.Bytes
import FS.Stream
import Test.FS.Util

-- --------------------------------------------------------------------------------
-- -- Utilities and Generators
-- --------------------------------------------------------------------------------
--
-- splitBytes : List Nat -> ByteString -> List ByteString
-- splitBytes []        bs = [bs]
-- splitBytes (x :: xs) bs =
--   let Just (y,z) := splitAt x bs | Nothing => splitBytes xs bs
--    in y :: splitBytes xs z
--
-- utf8Strings : Gen String
-- utf8Strings = string (linear 0 100) printableUnicode
--
-- stringAndSplits : Gen (HList [List Nat, String])
-- stringAndSplits = hlist [list (linear 0 10) smallNats, utf8Strings]
--
-- unicodeChunks : Gen (List ByteString)
-- unicodeChunks = (\[ns,s] => splitBytes ns (fromString s)) <$> stringAndSplits
--
-- --------------------------------------------------------------------------------
-- -- Properties
-- --------------------------------------------------------------------------------
--
-- prop_utf8chunks : Property
-- prop_utf8chunks =
--   property $ do
--     bss <- forAll unicodeChunks
--     fastConcat (streamList $ UTF8.chunks $ fromChunks $ map pure bss) ===
--       fastConcat bss
--
-- prop_utf8decode1 : Property
-- prop_utf8decode1 =
--   property $ do
--     str <- forAll utf8Strings
--     let bs := the ByteString $ fromString str
--     fastConcat (streamList $ UTF8.decode $ emit bs) === str
--
-- prop_utf8decode : Property
-- prop_utf8decode =
--   property $ do
--     [ns,str] <- forAll stringAndSplits
--     let cs := pure <$> splitBytes ns (fromString str)
--     (fastConcat $ streamList $ UTF8.decode $ fromChunks cs) === str
--
-- prop_lines1 : Property
-- prop_lines1 =
--   property $ do
--     bss <- forAll unicodeChunks
--     let str := toString (fastConcat bss)
--     streamList (map toString $ lines $ fromChunks $ map pure bss) === lines str
--
--------------------------------------------------------------------------------
-- Group
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup "FS.Bytes"
    [
--  [ ("prop_utf8chunks", prop_utf8chunks)
--     , ("prop_utf8decode1", prop_utf8decode1)
--     , ("prop_utf8decode", prop_utf8decode)
--     , ("prop_lines1", prop_lines1)
    ]
