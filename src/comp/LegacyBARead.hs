-- | Read the original .ba format. File discovery and invocation policy belong
-- to the driver; this codec preserves the baseline header and wire layout.
module LegacyBARead(readLegacyBAFile, readLegacyBAFileMaybe) where

import Warmup ()
import BinData(decode)
import Error(ErrMsg(..), ErrorHandle, bsErrorUnsafe)
import LegacyBA(LegacyABin, legacyBAHeader)
import Position(noPosition)
import qualified Data.ByteString as B

readLegacyBAFile :: ErrorHandle -> FilePath -> B.ByteString -> (LegacyABin, String)
readLegacyBAFile errh filename bytes =
    let hlen = B.length legacyBAHeader
    in if B.take hlen bytes == legacyBAHeader
       then (decode (B.drop hlen bytes), "")
       else bsErrorUnsafe errh [(noPosition, EBinFileVerMismatch filename)]

-- A matching header retains BinData's normal malformed-payload diagnostics.
readLegacyBAFileMaybe :: B.ByteString -> Maybe LegacyABin
readLegacyBAFileMaybe bytes =
    let hlen = B.length legacyBAHeader
    in if B.take hlen bytes == legacyBAHeader
       then Just (decode (B.drop hlen bytes))
       else Nothing
