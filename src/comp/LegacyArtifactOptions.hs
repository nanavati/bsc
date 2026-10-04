-- Frozen f092 .ba options. These fields preserve the legacy wire layout;
-- they are metadata, never phase execution configuration.
module LegacyArtifactOptions (LegacyArtifactOptions(..)) where

import Warmup ()
import Backend (Backend)
import FlagTypes

data LegacyArtifactOptions
    = NoLegacyArtifactOptions
    | LegacyArtifactOptions
        (Bool) -- 0: aggImpConds
        (Bool) -- 1: allowIncoherentMatches
        (Maybe Backend) -- 2: backend
        (Maybe String) -- 3: bdir
        (Bool) -- 4: biasMethodScheduling
        (String) -- 5: bluespecDir
        ([String]) -- 6: cIncPath
        ([String]) -- 7: cLibPath
        ([String]) -- 8: cLibs
        (Bool) -- 9: cDebug
        ([String]) -- 10: cFlags
        ([String]) -- 11: cxxFlags
        ([String]) -- 12: cppFlags
        ([String]) -- 13: linkFlags
        (Maybe String) -- 14: cdir
        (Bool) -- 15: cpp
        ([String]) -- 16: defines
        (MsgListFlag) -- 17: demoteErrors
        (Bool) -- 18: disableAssertions
        (Bool) -- 19: passThroughAssertions
        (Bool) -- 20: doICheck
        (Maybe (Maybe FilePath)) -- 21: dumpAll
        ([(DumpFlag, Maybe FilePath)]) -- 22: dumps
        (Bool) -- 23: enablePoisonPills
        (Maybe String) -- 24: entry
        (Int) -- 25: expandATSlimit
        (Bool) -- 26: expandIf
        (Maybe String) -- 27: fdir
        (Int) -- 28: finalcleanup
        (Bool) -- 29: genABin
        (Bool) -- 30: genABinVerilog
        ([String]) -- 31: genName
        (Bool) -- 32: genSysC
        ([String]) -- 33: ifcPathRaw
        ([String]) -- 34: ifcPath
        (Maybe String) -- 35: infoDir
        (Bool) -- 36: inlineBool
        (Bool) -- 37: inlineISyntax
        (Bool) -- 38: inlineSimple
        (Bool) -- 39: keepAddSize
        (Bool) -- 40: keepFires
        (Bool) -- 41: keepInlined
        (Maybe (DumpFlag, Maybe String)) -- 42: kill
        (Bool) -- 43: ifLift
        (Bool) -- 44: letGen
        (Int) -- 45: maxTIStackDepth
        (Bool) -- 46: methodBVI
        (Bool) -- 47: methodConf
        (Bool) -- 48: methodConditions
        (Bool) -- 49: neatNames
        (String) -- 50: oFile
        (Bool) -- 51: optAggInline
        (Bool) -- 52: optATS
        (Bool) -- 53: optAndOr
        (Bool) -- 54: optBitConst
        (Bool) -- 55: optBool
        (Bool) -- 56: optFinalPass
        (Bool) -- 57: optIfMux
        (Integer) -- 58: optIfMuxSize
        (Bool) -- 59: optJoinDefs
        (Bool) -- 60: optMux
        (Bool) -- 61: optMuxExpand
        (Bool) -- 62: optMuxConst
        (Bool) -- 63: optSched
        (Bool) -- 64: optUndet
        (Integer) -- 65: parallelSimLink
        (Bool) -- 66: printFlags
        (Bool) -- 67: printFlagsHidden
        (Bool) -- 68: printFlagsRaw
        (Bool) -- 69: preprocessOnly
        (MsgListFlag) -- 70: promoteWarnings
        (Bool) -- 71: readableMux
        (Integer) -- 72: redStepsWarnInterval
        (Integer) -- 73: redStepsMaxIntervals
        (Bool) -- 74: relaxMethodEarliness
        (Bool) -- 75: removeEmptyRules
        (Bool) -- 76: removeFalseRules
        (Bool) -- 77: removeInoutConnect
        (Bool) -- 78: removePrimModules
        (Bool) -- 79: removeCReg
        (Bool) -- 80: removeReg
        (Bool) -- 81: removeRWire
        (Bool) -- 82: removeCross
        (Bool) -- 83: removeStarvedRules
        (Bool) -- 84: removeUnusedMods
        (Bool) -- 85: removeVerilogDollar
        (String) -- 86: resetName
        (ResourceFlag) -- 87: resource
        (Bool) -- 88: rstGate
        (Bool) -- 89: ruleNameCheck
        (SATFlag) -- 90: satBackend
        (Bool) -- 91: schedConds
        (Bool) -- 92: schedDOT
        ([(String,String)]) -- 93: schedQueries
        (Bool) -- 94: showCSyntax
        (Bool) -- 95: showCodeGen
        (Bool) -- 96: showElabProgress
        (Bool) -- 97: showIESyntax
        (Bool) -- 98: showISyntax
        (Bool) -- 99: showModuleUse
        (Bool) -- 100: showRangeConflict
        (Bool) -- 101: showSchedule
        (Bool) -- 102: showStats
        (Bool) -- 103: showUpds
        (Bool) -- 104: simplifyCSyntax
        (Bool) -- 105: strictMethodSched
        (MsgListFlag) -- 106: suppressWarnings
        (Bool) -- 107: synthesize
        (Bool) -- 108: systemVerilogTasks
        (Bool) -- 109: tclShowHidden
        (Bool) -- 110: timeStamps
        (Bool) -- 111: showVersion
        (Bool) -- 112: testAssert
        (Bool) -- 113: unsafeAlwaysRdy
        (String) -- 114: unSpecTo
        (Bool) -- 115: updCheck
        (Bool) -- 116: useDPI
        (Bool) -- 117: useNegate
        (Bool) -- 118: usePrelude
        (Bool) -- 119: useProvisoSAT
        (Bool) -- 120: stdlibNames
        (Bool) -- 121: v95
        ([String]) -- 122: vFlags
        (Maybe String) -- 123: vdir
        ([String]) -- 124: vPathRaw
        ([String]) -- 125: vPath
        (Bool) -- 126: vpp
        (Maybe String) -- 127: vsim
        (Verbosity) -- 128: verbosity
        (Bool) -- 129: verilogDeclareAllFirst
        ([String]) -- 130: verilogFilter
        (Bool) -- 131: warnActionShadowing
        (Bool) -- 132: warnMethodUrgency
        (Bool) -- 133: warnUndetPred
