-- | Driver adapters for observation policy; compiler libraries use TopUtils.
module DriverTopUtils
    ( module TopUtils, start, dump, ddump, vdump, sdump, dumpStr
    , timestamp, timestampStr, stats, mkTimestampComment, mkGenFileHeader
    ) where

import TopUtils hiding (start, dump, ddump, vdump, sdump, dumpStr,
                        timestamp, timestampStr, stats,
                        mkTimestampComment, mkGenFileHeader)
import qualified TopUtils as T
import Flags (Flags, showVersion, timeStamps)
import Version (compilerVersion)
import qualified PhaseConfig as P
import qualified PhaseConfigDriver as D
import FlagTypes (DumpFlag)
import Error (ErrorHandle)
import Eval (NFData)
import PPrint (PPrint)
import PVPrint (PVPrint)

runConfig :: Flags -> P.PhaseConfig ()
runConfig flags = P.PhaseConfig (D.runFlags flags) (D.runOptions flags) ()

start :: Flags -> DumpFlag -> IO ()
start = T.start . runConfig

dump :: (PPrint a, NFData a) => ErrorHandle -> Flags -> TimeInfo -> DumpFlag -> DumpNames -> a -> IO TimeInfo
dump errh = T.dump errh . runConfig

ddump :: (PPrint a, NFData a) => ErrorHandle -> Flags -> TimeInfo -> DumpFlag -> DumpNames -> a -> IO TimeInfo
ddump errh = T.ddump errh . runConfig

vdump :: (PVPrint a, NFData a) => ErrorHandle -> Flags -> TimeInfo -> DumpFlag -> DumpNames -> a -> IO TimeInfo
vdump errh = T.vdump errh . runConfig

sdump :: (Show a, NFData a) => ErrorHandle -> Flags -> TimeInfo -> DumpFlag -> DumpNames -> a -> IO TimeInfo
sdump errh = T.sdump errh . runConfig

dumpStr :: ErrorHandle -> Flags -> TimeInfo -> DumpFlag -> DumpNames -> String -> IO TimeInfo
dumpStr errh = T.dumpStr errh . runConfig

timestamp :: Flags -> TimeInfo -> IO TimeInfo
timestamp = T.timestamp . runConfig

timestampStr :: Flags -> String -> TimeInfo -> IO TimeInfo
timestampStr = T.timestampStr . runConfig

stats :: Stats a => Flags -> DumpFlag -> a -> IO ()
stats = T.stats . runConfig

mkTimestampComment :: Flags -> IO String
mkTimestampComment = T.mkTimestampComment . timeStamps

mkGenFileHeader :: Flags -> IO [String]
mkGenFileHeader flags = T.mkGenFileHeader compilerVersion (showVersion flags) (timeStamps flags)
