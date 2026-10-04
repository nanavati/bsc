{-# LANGUAGE CPP #-}
-- | Source preprocessing and parsing, independent of compiler orchestration.
module ParseSource(parseFile, doCPP, chkParse, outlaw_sv_kws_as_classic_ids) where

import Control.Monad(when)
import System.Process(system)
import System.Exit(ExitCode(..))
import System.Directory(getCurrentDirectory)
import System.IO.Error(ioeGetErrorType)
import GHC.IO.Exception(IOErrorType(..))
import qualified Control.Exception as CE

import TmpNam(tmpNam, localTmpNam)
import FlagTypes
import qualified PhaseConfig as PC
import Backend
import Position(noPosition, filePosition)
import Error(internalError, EMsg, ErrMsg(..), ErrorHandle, bsError,
             exitFailWith, bsWarning, WMsg)
import PFPrint
import FStringCompat
import Lex
import Parse
import FileNameUtil(hasDotSuf, dropSuf, baseName, bscSrcSuffix,
                    createEncodedFullFilePath)
import FileIOUtil(readFileCatch, writeFileCatch, removeFileCatch)
import Id
import Parser.Classic(pPackage, errSyntax, classicWarnings)
import Parser.BSV(bsvParseString)
import CSyntax
import IOUtil(getEnvDef, progArgs)
import TopUtils

outlaw_sv_kws_as_classic_ids :: Bool
outlaw_sv_kws_as_classic_ids = "-outlaw-sv-kws-as-classic-ids" `elem` progArgs

doCPP :: ErrorHandle -> PC.PhaseConfig PC.ParseFlags -> String -> IO String
doCPP errh flags name =
    if PC.parseCpp (PC.phaseFlags flags)
    then do
        tempName <- tmpNam
        topNameRoot <- localTmpNam
        let topName = topNameRoot ++ ".c"
            tmpNameOut = tempName ++ ".out"
        writeFileCatch errh topName ("#include \""++name++"\"\n")
        comp <- getEnvDef "CC" dfltCCompile

{- If the compiler specified in the CC environment variable has a
spaces in its name, for example CC="/usr/local/my c compiler/bin/cc",
then this will fail.  You need to properly quote the spaces.  As a
side effect, (and in fact, this was the reason why), if you include
flags in the CC variable, for example CC="cc -g", then it will work.
-}

        let backend_def = case PC.parseBackend (PC.phaseFlags flags) of
                            Just Bluesim -> ["-D__GENC__"]
                            Just Verilog -> ["-D__GENVERILOG__"]
                            Nothing -> []
            cmd = unwords ([comp] ++ backend_def ++
                           ["-D__BSC__", "-E", "-nostdinc", "-traditional"] ++
                           -- the show function quotes things
                           (map show (PC.parseCppFlags (PC.phaseFlags flags)))
                           ++ [ topName, ">", tmpNameOut])
        when (PC.verbose flags) $ putStrLn ("exec: " ++ cmd)
        rc <- system cmd
        case rc of
         ExitSuccess -> do
                file <- readFileCatch errh noPosition tmpNameOut
                removeFileCatch errh topName
                removeFileCatch errh tmpNameOut
                return file
         ExitFailure n -> do
                removeFileCatch errh topName
                removeFileCatch errh tmpNameOut
                exitFailWith errh n
    else readFileCatch errh noPosition name

-- Parse a file: run CPP, dump CPP output, parse, check name, dump CSyntax, stats
-- Returns CPackage, TimeInfo, and warnings for passing to compilation
-- If fatal_name_mismatch is True, package name mismatch causes bsError (aborts)
-- If False, it's just a bsWarning
parseFile :: ErrorHandle -> PC.PhaseConfig PC.ParseFlags -> Bool -> FilePath -> IO (CPackage, TimeInfo, [WMsg])
parseFile errh flags fatal_name_mismatch fname = do
    let isClassic = hasDotSuf bscSrcSuffix fname

    t <- getNow
    let dumpnames = (Just (baseName (dropSuf fname)), Nothing, Nothing)

    -- parseSrc needs encoded path for position tracking
    pwd <- getCurrentDirectory
    let fname_encoded = createEncodedFullFilePath fname pwd

    start flags DFcpp
    file <- doCPP errh flags fname_encoded
    _ <- dumpStr errh flags t DFcpp dumpnames file

    -- parseSrc handles its own dump stages (DFparsed, DFvpp, etc.)
    (pkg@(CPackage i _ _ _ _ _ _), t', warns) <- parseSrc isClassic errh flags fname_encoded file

    -- Check for package name mismatch
    let reportMismatch = if fatal_name_mismatch then bsError else bsWarning
    -- Use getIdString rather than pfpString here: pfpString calls isClassic(),
    -- which reads a global IORef.  If it fires before compilePackage calls
    -- setSyntax, GHC can memoize the result as CLASSIC and corrupt the print
    -- mode for the entire subsequent compilation.  Package names are always
    -- simple unqualified identifiers, so getIdString is equivalent.
    when (getIdString i /= baseName (dropSuf fname)) $
         reportMismatch errh
             [(getPosition i, WFilePackageNameMismatch fname (getIdString i))]

    -- dump CSyntax
    when (PC.runShowCSyntax (PC.phaseRunOptions flags)) (putStrLnF (show pkg))
    -- dump stats
    stats flags DFparsed pkg

    return (pkg, t', warns)

-- wrapper to detect file encoding errors (which are detected lazily)
parseSrc :: Bool -> ErrorHandle -> PC.PhaseConfig PC.ParseFlags -> String -> String ->
            IO (CPackage, TimeInfo, [WMsg])
parseSrc classic errh flags filename inp = CE.handleJust isEncErr handleErr $ parseSrc' classic errh flags filename inp
    where isEncErr :: CE.IOException -> Maybe CE.IOException
          isEncErr e | InvalidArgument <- ioeGetErrorType e = Just e
                     | otherwise = Nothing
          handleErr _ = bsError errh [(filePosition $ mkFString filename, ENotUTF8)]

parseSrc' :: Bool -> ErrorHandle -> PC.PhaseConfig PC.ParseFlags -> String -> String ->
            IO (CPackage, TimeInfo, [WMsg])
parseSrc' True errh flags filename inp = do
  -- Classic parser
  t <- getNow
  let dumpnames = (Just (baseName (dropSuf filename)), Nothing, Nothing)
  start flags DFparsed
  let lflags = LFlags { lf_is_stdlib = PC.parseStdlibNames (PC.phaseFlags flags),
                        lf_allow_sv_kws = not outlaw_sv_kws_as_classic_ids }
  case chkParse pPackage (lexStart lflags (mkFString filename) inp) of
      Right pkg -> do t <- dump errh flags t DFparsed dumpnames pkg
                      let ws = classicWarnings pkg
                      return (pkg, t, ws)
      Left errs -> bsError errh errs
parseSrc' False errh flags filename inp =
  -- BSV parser
  bsvParseString errh flags filename (baseName $ dropSuf filename) inp

chkParse :: Parser [Token] a -> [Token] -> Either [EMsg] a
chkParse p ts =
    case parse p ts of
        Right ((m,_):_) -> Right m
        Left  (ss,ts)   -> Left [errSyntax (filter (not . null ) ss) ts]
        Right []        -> internalError "Depend.chkParse: Right []"

