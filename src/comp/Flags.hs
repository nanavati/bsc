module Flags(
             Flags(..),
             redSteps,
             ResourceFlag(..), SATFlag(..), MsgListFlag(..),

             DumpFlag(..),
             hasDump, hasDumpStrict, dumpInfo,

             Verbosity(..), extraVerbose, verbose, quiet,
             moreTalkative, lessTalkative, setVerbose,
        ) where

import Warmup ()
import Control.Applicative((<|>))
import Data.Maybe(isJust)

import Backend
import FlagTypes

-- -------------------------
-- Internal flags
--
-- Invocation-wide options owned by the driver; phases receive narrow projections.

data Flags = Flags {
        aggImpConds :: Bool,
        allowIncoherentMatches :: Bool,
        backend :: Maybe Backend,
        bdir :: Maybe String,
        biasMethodScheduling :: Bool,
        bluespecDir :: String,
        cIncPath :: [String],
        cLibPath :: [String],
        cLibs :: [String],
        cDebug :: Bool,
        cFlags :: [String],
        cxxFlags :: [String],
        cppFlags :: [String],
        linkFlags :: [String],
        cdir :: Maybe String,
        cpp :: Bool,
        defines :: [String],
        demoteErrors :: MsgListFlag,
        disableAssertions :: Bool,
        passThroughAssertions :: Bool,
        doICheck :: Bool,
        dumpAll :: Maybe (Maybe FilePath), -- maybe dump to file or stdout
        dumps :: [(DumpFlag, Maybe FilePath)], -- dump to file or stdout
        enablePoisonPills :: Bool,
        entry :: Maybe String,
        expandATSlimit :: Int,
        expandIf :: Bool,
        fdir :: Maybe String,
        finalcleanup :: Int,
        genABin :: Bool,
        genABinVerilog :: Bool,
        genName :: [String],
        genSysC :: Bool,
        ifcPathRaw :: [String],
        ifcPath :: [String],
        infoDir :: Maybe String,
        inlineBool :: Bool,
        inlineISyntax :: Bool,
        inlineSimple :: Bool,
        keepAddSize :: Bool,
        keepFires :: Bool,
        keepInlined :: Bool,
        kill :: Maybe (DumpFlag, Maybe String),
        ifLift :: Bool,
        letGen :: Bool,
        maxTIStackDepth :: Int,
        methodBVI :: Bool,
        methodConf :: Bool,
        methodConditions :: Bool,
        neatNames :: Bool,
        oFile :: String,
        optAggInline :: Bool,
        optATS :: Bool,
        optAndOr :: Bool,
        optBitConst :: Bool,
        optBool :: Bool,
        optFinalPass :: Bool,
        optIfMux :: Bool,
        optIfMuxSize :: Integer,
        optJoinDefs :: Bool,
        optMux :: Bool,
        optMuxExpand :: Bool,
        optMuxConst :: Bool,
        optSched :: Bool,
        optUndet :: Bool,
        parallelSimLink :: Integer,
        printFlags :: Bool,
        printFlagsHidden :: Bool,
        printFlagsRaw :: Bool,
        preprocessOnly :: Bool,
        promoteWarnings :: MsgListFlag,
        readableMux :: Bool,
        redStepsWarnInterval :: Integer,
        redStepsMaxIntervals :: Integer,
        relaxMethodEarliness :: Bool,
        removeEmptyRules :: Bool,
        removeFalseRules :: Bool,
        removeInoutConnect :: Bool,
        removePrimModules :: Bool,
        removeCReg :: Bool,
        removeReg :: Bool,
        removeRWire :: Bool,
        removeCross :: Bool,
        removeStarvedRules :: Bool,
        removeUnusedMods :: Bool,
        removeVerilogDollar :: Bool,
        resetName :: String,
        resource :: ResourceFlag,
        rstGate :: Bool,
        ruleNameCheck :: Bool,
        satBackend :: SATFlag,
        schedConds:: Bool,
        schedDOT :: Bool,
        schedQueries :: [(String,String)],
        showCSyntax :: Bool,
        showCodeGen :: Bool,
        showElabProgress :: Bool,
        showIESyntax :: Bool,
        showISyntax :: Bool,
        showModuleUse :: Bool,
        showRangeConflict :: Bool,
        showSchedule :: Bool,
        showStats :: Bool,
        showUpds :: Bool,
        simplifyCSyntax :: Bool,
        strictMethodSched :: Bool,
        suppressWarnings :: MsgListFlag,
        synthesize :: Bool,
        systemVerilogTasks :: Bool,
        tclShowHidden :: Bool,
        timeStamps :: Bool,
        showVersion :: Bool,
        testAssert :: Bool,
        unsafeAlwaysRdy :: Bool,
        unSpecTo :: String,
        updCheck :: Bool,
        useDPI :: Bool,
        useNegate :: Bool,
        usePrelude :: Bool,
        useProvisoSAT :: Bool,
        stdlibNames :: Bool,
        v95 :: Bool,
        vFlags :: [String],
        vdir :: Maybe String,
        vPathRaw :: [String],
        vPath :: [String],
        vpp :: Bool,
        vsim :: Maybe String,
        verbosity :: Verbosity,
        verilogDeclareAllFirst :: Bool,
        verilogFilter :: [String],
        warnActionShadowing :: Bool,
        warnMethodUrgency :: Bool,
        warnUndetPred :: Bool
        }
-- don't derive Show -- it causes an optimized ghc build to take a long time
--        deriving (Show)

extraVerbose :: Flags -> Bool
extraVerbose = (== ExtraVerbose) . verbosity

verbose :: Flags -> Bool
verbose = (>= Verbose) . verbosity

setVerbose :: Bool -> Flags -> Flags
setVerbose False f = f
setVerbose True  f = f { verbosity = max Verbose (verbosity f) }

quiet :: Flags -> Bool
quiet = (== Quiet) . verbosity

moreTalkative :: Flags -> Flags
moreTalkative f =
  case verbosity f of
    ExtraVerbose -> f
    v            -> f { verbosity = succ v }

lessTalkative :: Flags -> Flags
lessTalkative f =
  case verbosity f of
    Quiet -> f
    v     -> f { verbosity = pred v }

-----

-- The number of reduction steps is defined based on the interval
redSteps :: Flags -> Integer
redSteps flags = (redStepsWarnInterval flags) *
                 (redStepsMaxIntervals flags)

-----

hasDump :: Flags -> DumpFlag -> Bool
hasDump f d = (isJust $ dumpAll f) || (hasDumpStrict f d)

hasDumpStrict :: Flags -> DumpFlag -> Bool
hasDumpStrict f d = isJust $ lookup d (dumps f)

dumpInfo :: Flags -> DumpFlag -> Maybe (Maybe FilePath)
dumpInfo f d = lookup d (dumps f) <|> dumpAll f

-- -------------------------
