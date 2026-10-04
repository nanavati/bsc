-- | Driver-only projection of the frozen f092 compatibility metadata.
module LegacyOptionsDriver(freezeLegacyOptions, restoreLegacyOptions) where

import Warmup ()
import Flags(Flags(..))
import LegacyArtifactOptions

freezeLegacyOptions :: Flags -> LegacyArtifactOptions
freezeLegacyOptions flags = LegacyArtifactOptions
    (aggImpConds flags)
    (allowIncoherentMatches flags)
    (backend flags)
    (bdir flags)
    (biasMethodScheduling flags)
    (bluespecDir flags)
    (cIncPath flags)
    (cLibPath flags)
    (cLibs flags)
    (cDebug flags)
    (cFlags flags)
    (cxxFlags flags)
    (cppFlags flags)
    (linkFlags flags)
    (cdir flags)
    (cpp flags)
    (defines flags)
    (demoteErrors flags)
    (disableAssertions flags)
    (passThroughAssertions flags)
    (doICheck flags)
    (dumpAll flags)
    (dumps flags)
    (enablePoisonPills flags)
    (entry flags)
    (expandATSlimit flags)
    (expandIf flags)
    (fdir flags)
    (finalcleanup flags)
    (genABin flags)
    (genABinVerilog flags)
    (genName flags)
    (genSysC flags)
    (ifcPathRaw flags)
    (ifcPath flags)
    (infoDir flags)
    (inlineBool flags)
    (inlineISyntax flags)
    (inlineSimple flags)
    (keepAddSize flags)
    (keepFires flags)
    (keepInlined flags)
    (kill flags)
    (ifLift flags)
    (letGen flags)
    (maxTIStackDepth flags)
    (methodBVI flags)
    (methodConf flags)
    (methodConditions flags)
    (neatNames flags)
    (oFile flags)
    (optAggInline flags)
    (optATS flags)
    (optAndOr flags)
    (optBitConst flags)
    (optBool flags)
    (optFinalPass flags)
    (optIfMux flags)
    (optIfMuxSize flags)
    (optJoinDefs flags)
    (optMux flags)
    (optMuxExpand flags)
    (optMuxConst flags)
    (optSched flags)
    (optUndet flags)
    (parallelSimLink flags)
    (printFlags flags)
    (printFlagsHidden flags)
    (printFlagsRaw flags)
    (preprocessOnly flags)
    (promoteWarnings flags)
    (readableMux flags)
    (redStepsWarnInterval flags)
    (redStepsMaxIntervals flags)
    (relaxMethodEarliness flags)
    (removeEmptyRules flags)
    (removeFalseRules flags)
    (removeInoutConnect flags)
    (removePrimModules flags)
    (removeCReg flags)
    (removeReg flags)
    (removeRWire flags)
    (removeCross flags)
    (removeStarvedRules flags)
    (removeUnusedMods flags)
    (removeVerilogDollar flags)
    (resetName flags)
    (resource flags)
    (rstGate flags)
    (ruleNameCheck flags)
    (satBackend flags)
    (schedConds flags)
    (schedDOT flags)
    (schedQueries flags)
    (showCSyntax flags)
    (showCodeGen flags)
    (showElabProgress flags)
    (showIESyntax flags)
    (showISyntax flags)
    (showModuleUse flags)
    (showRangeConflict flags)
    (showSchedule flags)
    (showStats flags)
    (showUpds flags)
    (simplifyCSyntax flags)
    (strictMethodSched flags)
    (suppressWarnings flags)
    (synthesize flags)
    (systemVerilogTasks flags)
    (tclShowHidden flags)
    (timeStamps flags)
    (showVersion flags)
    (testAssert flags)
    (unsafeAlwaysRdy flags)
    (unSpecTo flags)
    (updCheck flags)
    (useDPI flags)
    (useNegate flags)
    (usePrelude flags)
    (useProvisoSAT flags)
    (stdlibNames flags)
    (v95 flags)
    (vFlags flags)
    (vdir flags)
    (vPathRaw flags)
    (vPath flags)
    (vpp flags)
    (vsim flags)
    (verbosity flags)
    (verilogDeclareAllFirst flags)
    (verilogFilter flags)
    (warnActionShadowing flags)
    (warnMethodUrgency flags)
    (warnUndetPred flags)

restoreLegacyOptions :: Flags -> LegacyArtifactOptions -> Flags
restoreLegacyOptions fallback NoLegacyArtifactOptions = fallback
restoreLegacyOptions fallback (LegacyArtifactOptions
    a_0
    a_1
    a_2
    a_3
    a_4
    a_5
    a_6
    a_7
    a_8
    a_9
    a_10
    a_11
    a_12
    a_13
    a_14
    a_15
    a_16
    a_17
    a_18
    a_19
    a_20
    a_21
    a_22
    a_23
    a_24
    a_25
    a_26
    a_27
    a_28
    a_29
    a_30
    a_31
    a_32
    a_33
    a_34
    a_35
    a_36
    a_37
    a_38
    a_39
    a_40
    a_41
    a_42
    a_43
    a_44
    a_45
    a_46
    a_47
    a_48
    a_49
    a_50
    a_51
    a_52
    a_53
    a_54
    a_55
    a_56
    a_57
    a_58
    a_59
    a_60
    a_61
    a_62
    a_63
    a_64
    a_65
    a_66
    a_67
    a_68
    a_69
    a_70
    a_71
    a_72
    a_73
    a_74
    a_75
    a_76
    a_77
    a_78
    a_79
    a_80
    a_81
    a_82
    a_83
    a_84
    a_85
    a_86
    a_87
    a_88
    a_89
    a_90
    a_91
    a_92
    a_93
    a_94
    a_95
    a_96
    a_97
    a_98
    a_99
    a_100
    a_101
    a_102
    a_103
    a_104
    a_105
    a_106
    a_107
    a_108
    a_109
    a_110
    a_111
    a_112
    a_113
    a_114
    a_115
    a_116
    a_117
    a_118
    a_119
    a_120
    a_121
    a_122
    a_123
    a_124
    a_125
    a_126
    a_127
    a_128
    a_129
    a_130
    a_131
    a_132
    a_133
    ) = fallback
    { aggImpConds = a_0
    , allowIncoherentMatches = a_1
    , backend = a_2
    , bdir = a_3
    , biasMethodScheduling = a_4
    , bluespecDir = a_5
    , cIncPath = a_6
    , cLibPath = a_7
    , cLibs = a_8
    , cDebug = a_9
    , cFlags = a_10
    , cxxFlags = a_11
    , cppFlags = a_12
    , linkFlags = a_13
    , cdir = a_14
    , cpp = a_15
    , defines = a_16
    , demoteErrors = a_17
    , disableAssertions = a_18
    , passThroughAssertions = a_19
    , doICheck = a_20
    , dumpAll = a_21
    , dumps = a_22
    , enablePoisonPills = a_23
    , entry = a_24
    , expandATSlimit = a_25
    , expandIf = a_26
    , fdir = a_27
    , finalcleanup = a_28
    , genABin = a_29
    , genABinVerilog = a_30
    , genName = a_31
    , genSysC = a_32
    , ifcPathRaw = a_33
    , ifcPath = a_34
    , infoDir = a_35
    , inlineBool = a_36
    , inlineISyntax = a_37
    , inlineSimple = a_38
    , keepAddSize = a_39
    , keepFires = a_40
    , keepInlined = a_41
    , kill = a_42
    , ifLift = a_43
    , letGen = a_44
    , maxTIStackDepth = a_45
    , methodBVI = a_46
    , methodConf = a_47
    , methodConditions = a_48
    , neatNames = a_49
    , oFile = a_50
    , optAggInline = a_51
    , optATS = a_52
    , optAndOr = a_53
    , optBitConst = a_54
    , optBool = a_55
    , optFinalPass = a_56
    , optIfMux = a_57
    , optIfMuxSize = a_58
    , optJoinDefs = a_59
    , optMux = a_60
    , optMuxExpand = a_61
    , optMuxConst = a_62
    , optSched = a_63
    , optUndet = a_64
    , parallelSimLink = a_65
    , printFlags = a_66
    , printFlagsHidden = a_67
    , printFlagsRaw = a_68
    , preprocessOnly = a_69
    , promoteWarnings = a_70
    , readableMux = a_71
    , redStepsWarnInterval = a_72
    , redStepsMaxIntervals = a_73
    , relaxMethodEarliness = a_74
    , removeEmptyRules = a_75
    , removeFalseRules = a_76
    , removeInoutConnect = a_77
    , removePrimModules = a_78
    , removeCReg = a_79
    , removeReg = a_80
    , removeRWire = a_81
    , removeCross = a_82
    , removeStarvedRules = a_83
    , removeUnusedMods = a_84
    , removeVerilogDollar = a_85
    , resetName = a_86
    , resource = a_87
    , rstGate = a_88
    , ruleNameCheck = a_89
    , satBackend = a_90
    , schedConds = a_91
    , schedDOT = a_92
    , schedQueries = a_93
    , showCSyntax = a_94
    , showCodeGen = a_95
    , showElabProgress = a_96
    , showIESyntax = a_97
    , showISyntax = a_98
    , showModuleUse = a_99
    , showRangeConflict = a_100
    , showSchedule = a_101
    , showStats = a_102
    , showUpds = a_103
    , simplifyCSyntax = a_104
    , strictMethodSched = a_105
    , suppressWarnings = a_106
    , synthesize = a_107
    , systemVerilogTasks = a_108
    , tclShowHidden = a_109
    , timeStamps = a_110
    , showVersion = a_111
    , testAssert = a_112
    , unsafeAlwaysRdy = a_113
    , unSpecTo = a_114
    , updCheck = a_115
    , useDPI = a_116
    , useNegate = a_117
    , usePrelude = a_118
    , useProvisoSAT = a_119
    , stdlibNames = a_120
    , v95 = a_121
    , vFlags = a_122
    , vdir = a_123
    , vPathRaw = a_124
    , vPath = a_125
    , vpp = a_126
    , vsim = a_127
    , verbosity = a_128
    , verilogDeclareAllFirst = a_129
    , verilogFilter = a_130
    , warnActionShadowing = a_131
    , warnMethodUrgency = a_132
    , warnUndetPred = a_133
    }
