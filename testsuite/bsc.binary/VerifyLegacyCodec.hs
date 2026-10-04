-- Build against the compatibility library, then pass .ba files produced by
-- the original f092 compiler. Every original byte must survive the split
-- decoder/encoder, including all legacy flags and optional embedded Verilog.
-- If the original codec also reorders intern-id-keyed maps while reading,
-- use --rewrite and compare its output against a fresh baseline-codec process;
-- never normalize fields or alter the serializer to make this check pass.
module Main (main) where

import BinData (encode)
import Error (initErrorHandle)
import LegacyBA (legacyBAHeader)
import LegacyBARead (readLegacyBAFile)

import Control.Monad (forM_, unless)
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC
import System.Environment (getArgs)
import System.Exit (die)

main :: IO ()
main = do
    args <- getArgs
    unless (legacyBAHeader == BC.pack "bsc-ba-20260712-1") $
        die "legacy format tag changed"
    errh <- initErrorHandle
    let rewritten path original =
            let (legacy, _) = readLegacyBAFile errh path original
            in legacyBAHeader `B.append` B.pack (encode legacy)
    case args of
        ["--rewrite", input, output] -> do
            original <- B.readFile input
            B.writeFile output (rewritten input original)
        [] -> die "usage: VerifyLegacyCodec [--rewrite INPUT.ba OUTPUT.ba | INPUT.ba ...]"
        paths -> forM_ paths $ \path -> do
            original <- B.readFile path
            unless (original == rewritten path original) $
                die ("re-encoded legacy bytes differ: " ++ path ++
                     " (compare a baseline codec process using --rewrite)")
            putStrLn ("PASS: original legacy bytes preserved: " ++ path)
