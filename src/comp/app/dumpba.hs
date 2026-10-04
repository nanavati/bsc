{-# LANGUAGE CPP #-}
module Main_dumpba(main) where

import Warmup ()
import Exceptions(withInternalErrorHandler)
import System.Environment(getArgs)

import LegacyBA ()
import LegacyBARead(readLegacyBAFile)
import PPrint
import Error(initErrorHandle)
import System.IO
import qualified Data.ByteString as BS

main :: IO ()
main = withInternalErrorHandler $ do
    errh <- initErrorHandle
    as <- getArgs
    case as of
     [mi] -> do
        file <- BS.readFile mi
        let (abi, hash) = readLegacyBAFile errh mi file
        hSetEncoding stdout utf8
        putStr (ppReadable abi)
        putStrLn ("Hash: " ++ hash)
     _ -> do
        putStr ("Usage: dumpba mod-id\n")
