module Test.FS.Bytes

import Control.Monad.Elin
import Data.Buffer.Indexed
import Data.ByteString
import Data.ByteVect
import Data.List1
import Data.String
import FS
import Test.FS.Util

--------------------------------------------------------------------------------
-- Utilities and Generators
--------------------------------------------------------------------------------

byteStrings : Gen ByteString
byteStrings = pack <$> byteLists

splitBytes : List Nat -> ByteString -> List ByteString
splitBytes []        bs = [bs]
splitBytes (x :: xs) bs =
  let Just (y,z) := splitAt x bs | Nothing => splitBytes xs bs
   in y :: splitBytes xs z

utf8Strings : Gen String
utf8Strings = string (linear 0 100) unicode

stringAndSplits : Gen (HList [List Nat, String])
stringAndSplits = hlist [list (linear 0 10) smallNats, utf8Strings]

unicodeChunks : Gen (List ByteString)
unicodeChunks = (\[ns,s] => splitBytes ns (fromString s)) <$> stringAndSplits

--------------------------------------------------------------------------------
-- Properties
--------------------------------------------------------------------------------

prop_utf8chunks : Property
prop_utf8chunks =
  property $ do
    bss <- forAll unicodeChunks
    fastConcat (outOnly (UTF8.chunks $ emits bss)) === fastConcat bss

prop_utf8decode1 : Property
prop_utf8decode1 =
  property $ do
    str <- forAll utf8Strings
    let bs := the ByteString $ fromString str
    fastConcat (outOnly (UTF8.decode $ emit bs)) === str

prop_utf8decode : Property
prop_utf8decode =
  property $ do
    [ns,str] <- forAll stringAndSplits
    let cs := splitBytes ns (fromString str)
    (fastConcat $ outOnly $ UTF8.decode $ emits cs) === str

prop_lines1 : Property
prop_lines1 =
  property $ do
    bss <- forAll unicodeChunks
    let bs := fastConcat bss
    when (bs.size > 0) $
      (join $ outOnly $ lines $ emits bss) === split 10 bs

prop_split : Property
prop_split =
  property $ do
    bss <- forAll unicodeChunks
    let bs := fastConcat bss
    when (bs.size > 0) $
      (join $ outOnly $ C.split (10 ==) $ emits bss) === split 10 bs

prop_breakAtSubstring : Property
prop_breakAtSubstring =
  property $ do
    [ss,bs] <- forAll $ hlist [byteStrings,list (linear 0 10) byteStrings]
    (fastConcat $ outOnly $ ignore $ Bytes.breakAtSubstring ss (emits bs)) ===
      fst (breakAtSubstring ss $ fastConcat bs)

bssTotal : ByteString -> Pull f ByteString es r -> Pull f ByteString es r
bssTotal ss p =
  breakAtSubstring ss p >>= \case
    Left  v => pure v
    Right q => emit ss >> q

prop_breakAtSubstringTotal : Property
prop_breakAtSubstringTotal =
  property $ do
    [ss,bs] <- forAll $ hlist [byteStrings,list (linear 0 10) byteStrings]
    (fastConcat $ outOnly $ bssTotal ss (emits bs)) ===
      fastConcat bs

--------------------------------------------------------------------------------
-- Group
--------------------------------------------------------------------------------

export
props : Group
props =
  MkGroup "FS.Bytes"
    [ ("prop_utf8chunks", prop_utf8chunks)
    , ("prop_utf8decode1", prop_utf8decode1)
    , ("prop_utf8decode", prop_utf8decode)
    , ("prop_lines1", prop_lines1)
    , ("prop_split", prop_split)
    , ("prop_breakAtSubstring", prop_breakAtSubstring)
    , ("prop_breakAtSubstringTotal", prop_breakAtSubstringTotal)
    ]
