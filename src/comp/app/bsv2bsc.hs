module Main_bsv2bsc(main) where

import Warmup ()
import Exceptions(withInternalErrorHandler)
import System.Environment

import Parser.BSV(bsvParseString)
import PPrint
import FlagsDefaults(defaultFlags)
import PhaseConfigDriver(parseConfig)
import Error(initErrorHandle)

main :: IO ()
main = withInternalErrorHandler $
    do args <- getArgs
       case args of
         [] -> getContents >>= bsv2bsc "-"
         [fn] -> readFile fn >>= bsv2bsc fn
         _ -> error "usage: bsv2bsc filename"

bsv2bsc :: String -> String -> IO ()
bsv2bsc filename text =
    do errh <- initErrorHandle
       (pkg, _, _) <- bsvParseString errh (parseConfig (defaultFlags "")) filename (stripExt filename) text
       putStrLn (ppReadable pkg)

stripExt :: String -> String
stripExt filename =
    case reverse filename of
    ('v':'s':'b':'.':revBase) -> reverse revBase
    _ -> filename
