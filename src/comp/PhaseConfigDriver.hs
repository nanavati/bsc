-- | Driver-owned projection of invocation-wide options into phase inputs.
-- Internal libraries depend on PhaseConfig and cannot recover global Flags.
module PhaseConfigDriver
    ( module PhaseConfig
    , parseConfig
    , reduceConfig
    , typecheckConfig
    , internalConfig
    , elabConfig
    , schedConfig
    , verilogGenConfig
    , bluesimGenConfig
    , hostCompileConfig
    , verilogLinkConfig
    , bluesimLinkConfig
    , foreignGenConfig
    , typeSolverFlags
    , runFlags, runOptions
    ) where

import Flags (Flags)
import qualified Flags as F
import PhaseConfig
import Version (compilerVersion)

typeSolverFlags :: Flags -> TypeSolverFlags
typeSolverFlags flags = TypeSolverFlags
    { typeSolverMaxTIStackDepth = F.maxTIStackDepth flags
    , typeSolverUseProvisoSAT = F.useProvisoSAT flags
    , typeSolverSatBackend = F.satBackend flags
    }


runFlags :: Flags -> RunFlags
runFlags flags = RunFlags
    { runCompilerVersion = compilerVersion
    , runBluespecDir = F.bluespecDir flags
    , runPromoteWarnings = F.promoteWarnings flags
    , runDemoteErrors = F.demoteErrors flags
    , runSuppressWarnings = F.suppressWarnings flags
    , runEnablePoisonPills = F.enablePoisonPills flags
    , runDoICheck = F.doICheck flags
    , runKill = F.kill flags
    }

runOptions :: Flags -> RunOptions
runOptions flags = RunOptions
    { runVerbosity = F.verbosity flags
    , runDumpAll = F.dumpAll flags
    , runDumps = F.dumps flags
    , runShowStats = F.showStats flags
    , runShowCodeGen = F.showCodeGen flags
    , runShowCSyntax = F.showCSyntax flags
    , runShowISyntax = F.showISyntax flags
    , runShowIESyntax = F.showIESyntax flags
    , runShowElabProgress = F.showElabProgress flags
    , runShowModuleUse = F.showModuleUse flags
    , runShowUpds = F.showUpds flags
    , runTclShowHidden = F.tclShowHidden flags
    , runInfoDir = F.infoDir flags
    , runSchedDOT = F.schedDOT flags
    , runShowSchedule = F.showSchedule flags
    }

parseConfig :: Flags -> PhaseConfig ParseFlags
parseConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    ParseFlags
        { parseCpp = F.cpp flags
        , parseCppFlags = F.cppFlags flags
        , parseBackend = F.backend flags
        , parseVpp = F.vpp flags
        , parseDefines = F.defines flags
        , parseIfcPath = F.ifcPath flags
        , parseStdlibNames = F.stdlibNames flags
        , parseDisableAssertions = F.disableAssertions flags
        , parsePassThroughAssertions = F.passThroughAssertions flags
        , parseGenName = F.genName flags
        , parsePreprocessOnly = F.preprocessOnly flags
        }

reduceConfig :: Flags -> PhaseConfig ReduceFlags
reduceConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    ReduceFlags
        { reduceMaxTIStackDepth = F.maxTIStackDepth flags
        , reduceUseProvisoSAT = F.useProvisoSAT flags
        , reduceSatBackend = F.satBackend flags
        , reduceResetName = F.resetName flags
        , reduceBackend = F.backend flags
        , reduceGenName = F.genName flags
        , reduceUsePrelude = F.usePrelude flags
        , reduceIfcPath = F.ifcPath flags
        }

typecheckConfig :: Flags -> PhaseConfig TypecheckFlags
typecheckConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    TypecheckFlags
        { typecheckMaxTIStackDepth = F.maxTIStackDepth flags
        , typecheckUseProvisoSAT = F.useProvisoSAT flags
        , typecheckSatBackend = F.satBackend flags
        , typecheckAllowIncoherentMatches = F.allowIncoherentMatches flags
        , typecheckLetGen = F.letGen flags
        }

internalConfig :: Flags -> PhaseConfig InternalFlags
internalConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    InternalFlags
        { internalMaxTIStackDepth = F.maxTIStackDepth flags
        , internalUseProvisoSAT = F.useProvisoSAT flags
        , internalSatBackend = F.satBackend flags
        , internalSimplifyCSyntax = F.simplifyCSyntax flags
        , internalBackend = F.backend flags
        , internalUseDPI = F.useDPI flags
        , internalBdir = F.bdir flags
        , internalVdir = F.vdir flags
        , internalShowVersion = F.showVersion flags
        , internalTimeStamps = F.timeStamps flags
        , internalTestAssert = F.testAssert flags
        }

elabConfig :: Flags -> PhaseConfig ElabFlags
elabConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    ElabFlags
        { elabBackend = F.backend flags
        , elabBdir = F.bdir flags
        , elabFdir = F.fdir flags
        , elabAggImpConds = F.aggImpConds flags
        , elabMethodConditions = F.methodConditions flags
        , elabResetName = F.resetName flags
        , elabRuleNameCheck = F.ruleNameCheck flags
        , elabInlineISyntax = F.inlineISyntax flags
        , elabInlineSimple = F.inlineSimple flags
        , elabOptBool = F.optBool flags
        , elabExpandIf = F.expandIf flags
        , elabIfLift = F.ifLift flags
        , elabRemoveFalseRules = F.removeFalseRules flags
        , elabRemoveEmptyRules = F.removeEmptyRules flags
        , elabUseProvisoSAT = F.useProvisoSAT flags
        , elabSatBackend = F.satBackend flags
        , elabRedStepsWarnInterval = F.redStepsWarnInterval flags
        , elabRedStepsMaxIntervals = F.redStepsMaxIntervals flags
        , elabMaxTIStackDepth = F.maxTIStackDepth flags
        , elabLetGen = F.letGen flags
        , elabWarnUndetPred = F.warnUndetPred flags
        , elabExpandATSlimit = F.expandATSlimit flags
        , elabOptFinalPass = F.optFinalPass flags
        }

schedConfig :: Flags -> PhaseConfig SchedFlags
schedConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    SchedFlags
        { schedBackend = F.backend flags
        , schedBiasMethodScheduling = F.biasMethodScheduling flags
        , schedGenABin = F.genABin flags
        , schedRelaxMethodEarliness = F.relaxMethodEarliness flags
        , schedResource = F.resource flags
        , schedSatBackend = F.satBackend flags
        , schedSchedConds = F.schedConds flags
        , schedSchedQueries = F.schedQueries flags
        , schedStrictMethodSched = F.strictMethodSched flags
        , schedUnsafeAlwaysRdy = F.unsafeAlwaysRdy flags
        , schedRemoveStarvedRules = F.removeStarvedRules flags
        , schedWarnActionShadowing = F.warnActionShadowing flags
        , schedWarnMethodUrgency = F.warnMethodUrgency flags
        , schedShowRangeConflict = F.showRangeConflict flags
        , schedExpandATSlimit = F.expandATSlimit flags
        , schedTimeStamps = F.timeStamps flags
        , schedShowVersion = F.showVersion flags
        }

verilogGenConfig :: Flags -> PhaseConfig VerilogGenFlags
verilogGenConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    VerilogGenFlags
        { verilogGenUseDPI = F.useDPI flags
        , verilogGenOptUndet = F.optUndet flags
        , verilogGenRemoveRWire = F.removeRWire flags
        , verilogGenRemoveCross = F.removeCross flags
        , verilogGenRemoveCReg = F.removeCReg flags
        , verilogGenRemoveReg = F.removeReg flags
        , verilogGenRemoveInoutConnect = F.removeInoutConnect flags
        , verilogGenRemoveUnusedMods = F.removeUnusedMods flags
        , verilogGenRemovePrimModules = F.removePrimModules flags
        , verilogGenRemoveVerilogDollar = F.removeVerilogDollar flags
        , verilogGenKeepFires = F.keepFires flags
        , verilogGenKeepInlined = F.keepInlined flags
        , verilogGenKeepAddSize = F.keepAddSize flags
        , verilogGenInlineBool = F.inlineBool flags
        , verilogGenOptATS = F.optATS flags
        , verilogGenOptSched = F.optSched flags
        , verilogGenOptJoinDefs = F.optJoinDefs flags
        , verilogGenOptIfMux = F.optIfMux flags
        , verilogGenOptIfMuxSize = F.optIfMuxSize flags
        , verilogGenOptMux = F.optMux flags
        , verilogGenOptMuxExpand = F.optMuxExpand flags
        , verilogGenOptMuxConst = F.optMuxConst flags
        , verilogGenOptBitConst = F.optBitConst flags
        , verilogGenOptAggInline = F.optAggInline flags
        , verilogGenOptAndOr = F.optAndOr flags
        , verilogGenOptFinalPass = F.optFinalPass flags
        , verilogGenSatBackend = F.satBackend flags
        , verilogGenSynthesize = F.synthesize flags
        , verilogGenUseNegate = F.useNegate flags
        , verilogGenReadableMux = F.readableMux flags
        , verilogGenFinalcleanup = F.finalcleanup flags
        , verilogGenUnSpecTo = F.unSpecTo flags
        , verilogGenSystemVerilogTasks = F.systemVerilogTasks flags
        , verilogGenV95 = F.v95 flags
        , verilogGenVerilogDeclareAllFirst = F.verilogDeclareAllFirst flags
        , verilogGenVdir = F.vdir flags
        , verilogGenVerilogFilter = F.verilogFilter flags
        , verilogGenIfcPath = F.ifcPath flags
        , verilogGenMethodConf = F.methodConf flags
        , verilogGenMethodBVI = F.methodBVI flags
        , verilogGenTimeStamps = F.timeStamps flags
        , verilogGenShowVersion = F.showVersion flags
        }

bluesimGenConfig :: Flags -> PhaseConfig BluesimGenFlags
bluesimGenConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    BluesimGenFlags
        { bluesimGenGenSysC = F.genSysC flags
        , bluesimGenResetName = F.resetName flags
        , bluesimGenUnSpecTo = F.unSpecTo flags
        , bluesimGenKeepFires = F.keepFires flags
        , bluesimGenTimeStamps = F.timeStamps flags
        , bluesimGenShowVersion = F.showVersion flags
        , bluesimGenIfcPath = F.ifcPath flags
        , bluesimGenCdir = F.cdir flags
        , bluesimGenOptUndet = F.optUndet flags
        }

hostCompileConfig :: Flags -> PhaseConfig HostCompileFlags
hostCompileConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    HostCompileFlags
        { hostCompileGenSysC = F.genSysC flags
        , hostCompileCxxFlags = F.cxxFlags flags
        , hostCompileCDebug = F.cDebug flags
        , hostCompileCIncPath = F.cIncPath flags
        , hostCompileCFlags = F.cFlags flags
        , hostCompileCdir = F.cdir flags
        , hostCompileParallelSimLink = F.parallelSimLink flags
        }

verilogLinkConfig :: Flags -> PhaseConfig VerilogLinkFlags
verilogLinkConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    VerilogLinkFlags
        { verilogLinkCLibPath = F.cLibPath flags
        , verilogLinkCLibs = F.cLibs flags
        , verilogLinkDefines = F.defines flags
        , verilogLinkVPath = F.vPath flags
        , verilogLinkOFile = F.oFile flags
        , verilogLinkVFlags = F.vFlags flags
        , verilogLinkLinkFlags = F.linkFlags flags
        , verilogLinkUseDPI = F.useDPI flags
        , verilogLinkVsim = F.vsim flags
        }

bluesimLinkConfig :: Flags -> PhaseConfig BluesimLinkFlags
bluesimLinkConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    BluesimLinkFlags
        { bluesimLinkOFile = F.oFile flags
        , bluesimLinkCLibPath = F.cLibPath flags
        , bluesimLinkCLibs = F.cLibs flags
        , bluesimLinkLinkFlags = F.linkFlags flags
        , bluesimLinkCDebug = F.cDebug flags
        , bluesimLinkTimeStamps = F.timeStamps flags
        }

foreignGenConfig :: Flags -> PhaseConfig ForeignGenFlags
foreignGenConfig flags = PhaseConfig (runFlags flags) (runOptions flags)
    ForeignGenFlags
        { foreignGenUseDPI = F.useDPI flags
        , foreignGenVPath = F.vPath flags
        , foreignGenVdir = F.vdir flags
        , foreignGenTimeStamps = F.timeStamps flags
        , foreignGenShowVersion = F.showVersion flags
        }
