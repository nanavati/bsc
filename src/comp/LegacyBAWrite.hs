-- | Write the original .ba format without depending on input discovery.
module LegacyBAWrite(genLegacyBAFile) where

import Warmup ()
import BinData(encode)
import Error(ErrorHandle)
import FileIOUtil(writeBinaryFileCatch)
import LegacyBA(LegacyABin, legacyBAHeader)
import qualified Data.ByteString as B

genLegacyBAFile :: ErrorHandle -> FilePath ->
                   LegacyABin -> IO ()
genLegacyBAFile errh filename legacy =
    writeBinaryFileCatch errh filename
        (B.unpack legacyBAHeader ++ encode legacy)
