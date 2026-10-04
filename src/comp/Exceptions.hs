{-# LANGUAGE CPP #-}
module Exceptions (bsCatch, withInternalErrorHandler) where

import Warmup ()
import qualified Control.Exception as CE
import ErrorUtil(InternalCompilerError(..))
import Version(bscVersionStr)
import Control.Monad(msum)
import System.IO.Error(ioeGetErrorString)
import System.IO(hFlush, stdout, hPutStr, stderr)
import System.Exit(ExitCode, exitFailure, exitWith)

bsCatch :: IO a -> IO a
bsCatch fn = CE.catch (withInternalErrorHandler fn) bscExceptions
        where bscExceptions :: CE.SomeException -> IO a
              bscExceptions e = let act = msum [ handleIOException e, handleErrorCall e, handleExit e]
                                in case act of
                                     (Just ioact) -> ioact
                                     Nothing      -> CE.throwIO e
              -- these are in the Maybe monad
              handleIOException ex =
                  do err <- (CE.fromException ex)::(Maybe CE.IOException)
                     let msg = (ioeGetErrorString err)
                     return $ hFlush stdout >> hPutStr stderr msg >> exitFailure
              handleErrorCall ex =
                  do (CE.ErrorCall msg) <- (CE.fromException ex)::(Maybe CE.ErrorCall)
                     return $ hFlush stdout >> hPutStr stderr msg >> exitFailure
              handleExit ex =
                  do exitcode <- (CE.fromException ex)::(Maybe ExitCode)
                     return $ exitWith exitcode


-- Preserve the established internal-error diagnostic and exit status at the
-- driver boundary. Compiler libraries need only the structured payload.
withInternalErrorHandler :: IO a -> IO a
withInternalErrorHandler action = CE.catch action reportInternalError

reportInternalError :: InternalCompilerError -> IO a
reportInternalError (InternalCompilerError msg_data) =
    let title = "Internal Bluespec Compiler Error"
        desc1 = "Please report this failure to the BSC developers, by opening a ticket\n" ++
                "in the issue database: https://github.com/B-Lang-org/bsc/issues\n"
        desc2 = "The following internal error message should be included in your\n" ++
                "correspondence along with any other relevant details:\n"
        ver = bscVersionStr True ++ "\n"
        msg_str = title ++ ":\n" ++ desc1 ++ desc2 ++ ver ++ msg_data ++ "\n"
    in hPutStr stderr msg_str >> exitFailure
