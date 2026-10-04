-- | Explicit configuration inputs for compiler phases. The CLI's historical
-- 'Flags' record is projected at orchestration boundaries; no phase value
-- retains that record or a function which can recover unrelated settings.
--
-- 'RunOptions' contains observation and ordinary dump requests. These do not
-- belong in a future primary-artifact cache key. 'RunFlags' carries failure
-- policy and explicit compiler identity; metadata fields consumed in outputs
-- or compatibility checks do belong in those phase result keys. Algorithm and
-- product choices live in the appropriate phase record. This module does not
-- implement caching.
module PhaseConfig
    ( PhaseConfig(..)
    , RunFlags(..)
    , RunOptions(..)
    , TypeSolverFlags(..)
    , ParseFlags(..)
    , ReduceFlags(..)
    , TypecheckFlags(..)
    , InternalFlags(..)
    , ElabFlags(..)
    , SchedFlags(..)
    , VerilogGenFlags(..)
    , BluesimGenFlags(..)
    , HostCompileFlags(..)
    , VerilogLinkFlags(..)
    , BluesimLinkFlags(..)
    , ForeignGenFlags(..)
    , ForeignWrapperFlags(..)
    , internalForeignWrapperConfig, verilogForeignWrapperConfig
    , foreignGenWrapperConfig
    , internalTypecheckFlags
    , typecheckTypeSolverFlags, reduceTypeSolverFlags
    , internalTypeSolverFlags, elabTypeSolverFlags, elabTypecheckFlags
    , verbose, quiet, extraVerbose
    , hasDump, hasDumpStrict, dumpInfo
    , phaseCompilerVersion
    ) where

import Backend (Backend)
import CompilerVersion (CompilerVersion)
import Control.Applicative ((<|>))
import Data.Maybe (isJust)
import FlagTypes (DumpFlag, MsgListFlag, ResourceFlag, SATFlag, Verbosity(..))

-- | Common failure and execution policy, with driver-supplied compiler
-- identity for generated metadata and compatibility checks. This value is an
-- explicit input, not part of the library implementation fingerprint.


data RunFlags = RunFlags
    { runCompilerVersion :: CompilerVersion
    , runBluespecDir :: String
    , runPromoteWarnings :: MsgListFlag
    , runDemoteErrors :: MsgListFlag
    , runSuppressWarnings :: MsgListFlag
    , runEnablePoisonPills :: Bool
    , runDoICheck :: Bool
    , runKill :: Maybe (DumpFlag, Maybe String)
    } deriving (Eq, Show)


-- | Observation settings shared by the phase drivers.


data RunOptions = RunOptions
    { runVerbosity :: Verbosity
    , runDumpAll :: Maybe (Maybe FilePath)
    , runDumps :: [(DumpFlag, Maybe FilePath)]
    , runShowStats :: Bool
    , runShowCodeGen :: Bool
    , runShowCSyntax :: Bool
    , runShowISyntax :: Bool
    , runShowIESyntax :: Bool
    , runShowElabProgress :: Bool
    , runShowModuleUse :: Bool
    , runShowUpds :: Bool
    , runTclShowHidden :: Bool
    , runInfoDir :: Maybe String
    , runSchedDOT :: Bool
    , runShowSchedule :: Bool
    } deriving (Eq, Show)


-- | The complete explicit input to one phase. It is deliberately independent
-- of the invocation-wide 'Flags' representation owned by the driver.
data PhaseConfig a = PhaseConfig
    { phaseRunFlags :: RunFlags
    , phaseRunOptions :: RunOptions
    , phaseFlags :: a
    } deriving (Eq, Show)

-- | The driver identity carried into phases without a generated-module import.
phaseCompilerVersion :: PhaseConfig a -> CompilerVersion
phaseCompilerVersion = runCompilerVersion . phaseRunFlags

-- | Solver policy shared with internal checks of generated expressions.
-- These checks choose their own language and recovery policies; they do not
-- inherit the source package's complete typechecking or execution settings.
data TypeSolverFlags = TypeSolverFlags
    { typeSolverMaxTIStackDepth :: Int
    , typeSolverUseProvisoSAT :: Bool
    , typeSolverSatBackend :: SATFlag
    } deriving (Eq, Show)

data ParseFlags = ParseFlags
    { parseCpp :: Bool
    , parseCppFlags :: [String]
    , parseBackend :: Maybe Backend
    , parseVpp :: Bool
    , parseDefines :: [String]
    , parseIfcPath :: [String]
    , parseStdlibNames :: Bool
    , parseDisableAssertions :: Bool
    , parsePassThroughAssertions :: Bool
    , parseGenName :: [String]
    , parsePreprocessOnly :: Bool
    } deriving (Eq, Show)

data ReduceFlags = ReduceFlags
    { reduceMaxTIStackDepth :: Int
    , reduceUseProvisoSAT :: Bool
    , reduceSatBackend :: SATFlag
    , reduceResetName :: String
    , reduceBackend :: Maybe Backend
    , reduceGenName :: [String]
    , reduceUsePrelude :: Bool
    , reduceIfcPath :: [String]
    } deriving (Eq, Show)

data TypecheckFlags = TypecheckFlags
    { typecheckMaxTIStackDepth :: Int
    , typecheckUseProvisoSAT :: Bool
    , typecheckSatBackend :: SATFlag
    , typecheckAllowIncoherentMatches :: Bool
    , typecheckLetGen :: Bool
    } deriving (Eq, Show)

data InternalFlags = InternalFlags
    { internalMaxTIStackDepth :: Int
    , internalUseProvisoSAT :: Bool
    , internalSatBackend :: SATFlag
    , internalSimplifyCSyntax :: Bool
    , internalBackend :: Maybe Backend
    , internalUseDPI :: Bool
    , internalBdir :: Maybe String
    , internalVdir :: Maybe String
    , internalShowVersion :: Bool
    , internalTimeStamps :: Bool
    , internalTestAssert :: Bool
    } deriving (Eq, Show)

-- optFinalPass also preserves the optional LambdaCalc/SAL dump lowering.


data ElabFlags = ElabFlags
    { elabBackend :: Maybe Backend
    , elabBdir :: Maybe String
    , elabFdir :: Maybe String
    , elabAggImpConds :: Bool
    , elabMethodConditions :: Bool
    , elabResetName :: String
    , elabRuleNameCheck :: Bool
    , elabInlineISyntax :: Bool
    , elabInlineSimple :: Bool
    , elabOptBool :: Bool
    , elabExpandIf :: Bool
    , elabIfLift :: Bool
    , elabRemoveFalseRules :: Bool
    , elabRemoveEmptyRules :: Bool
    , elabUseProvisoSAT :: Bool
    , elabSatBackend :: SATFlag
    , elabRedStepsWarnInterval :: Integer
    , elabRedStepsMaxIntervals :: Integer
    , elabMaxTIStackDepth :: Int
    , elabLetGen :: Bool
    , elabWarnUndetPred :: Bool
    , elabExpandATSlimit :: Int
    , elabOptFinalPass :: Bool
    } deriving (Eq, Show)

-- genABin and schedQueries affect relation coverage, not just reporting.


data SchedFlags = SchedFlags
    { schedBackend :: Maybe Backend
    , schedBiasMethodScheduling :: Bool
    , schedGenABin :: Bool
    , schedRelaxMethodEarliness :: Bool
    , schedResource :: ResourceFlag
    , schedSatBackend :: SATFlag
    , schedSchedConds :: Bool
    , schedSchedQueries :: [(String,String)]
    , schedStrictMethodSched :: Bool
    , schedUnsafeAlwaysRdy :: Bool
    , schedRemoveStarvedRules :: Bool
    , schedWarnActionShadowing :: Bool
    , schedWarnMethodUrgency :: Bool
    , schedShowRangeConflict :: Bool
    , schedExpandATSlimit :: Int
    , schedTimeStamps :: Bool
    , schedShowVersion :: Bool
    } deriving (Eq, Show)

-- | Verilog preparation and emission share these semantic inputs. The target
-- is intrinsic to the backend, so no invocation-wide backend selector is kept.
data VerilogGenFlags = VerilogGenFlags
    { verilogGenUseDPI :: Bool
    , verilogGenOptUndet :: Bool
    , verilogGenRemoveRWire :: Bool
    , verilogGenRemoveCross :: Bool
    , verilogGenRemoveCReg :: Bool
    , verilogGenRemoveReg :: Bool
    , verilogGenRemoveInoutConnect :: Bool
    , verilogGenRemoveUnusedMods :: Bool
    , verilogGenRemovePrimModules :: Bool
    , verilogGenRemoveVerilogDollar :: Bool
    , verilogGenKeepFires :: Bool
    , verilogGenKeepInlined :: Bool
    , verilogGenKeepAddSize :: Bool
    , verilogGenInlineBool :: Bool
    , verilogGenOptATS :: Bool
    , verilogGenOptSched :: Bool
    , verilogGenOptJoinDefs :: Bool
    , verilogGenOptIfMux :: Bool
    , verilogGenOptIfMuxSize :: Integer
    , verilogGenOptMux :: Bool
    , verilogGenOptMuxExpand :: Bool
    , verilogGenOptMuxConst :: Bool
    , verilogGenOptBitConst :: Bool
    , verilogGenOptAggInline :: Bool
    , verilogGenOptAndOr :: Bool
    , verilogGenOptFinalPass :: Bool
    , verilogGenSatBackend :: SATFlag
    , verilogGenSynthesize :: Bool
    , verilogGenUseNegate :: Bool
    , verilogGenReadableMux :: Bool
    , verilogGenFinalcleanup :: Int
    , verilogGenUnSpecTo :: String
    , verilogGenSystemVerilogTasks :: Bool
    , verilogGenV95 :: Bool
    , verilogGenVerilogDeclareAllFirst :: Bool
    , verilogGenVdir :: Maybe String
    , verilogGenVerilogFilter :: [String]
    , verilogGenIfcPath :: [String]
    , verilogGenMethodConf :: Bool
    , verilogGenMethodBVI :: Bool
    , verilogGenTimeStamps :: Bool
    , verilogGenShowVersion :: Bool
    } deriving (Eq, Show)

-- | Bluesim preparation and emission, including preparation of child modules
-- loaded from saved module/schedule pairs. The target is intrinsic here too.


data BluesimGenFlags = BluesimGenFlags
    { bluesimGenGenSysC :: Bool
    , bluesimGenResetName :: String
    , bluesimGenUnSpecTo :: String
    , bluesimGenKeepFires :: Bool
    , bluesimGenTimeStamps :: Bool
    , bluesimGenShowVersion :: Bool
    , bluesimGenIfcPath :: [String]
    , bluesimGenCdir :: Maybe String
    , bluesimGenOptUndet :: Bool
    } deriving (Eq, Show)

data HostCompileFlags = HostCompileFlags
    { hostCompileGenSysC :: Bool
    , hostCompileCxxFlags :: [String]
    , hostCompileCDebug :: Bool
    , hostCompileCIncPath :: [String]
    , hostCompileCFlags :: [String]
    , hostCompileCdir :: Maybe String
    , hostCompileParallelSimLink :: Integer
    } deriving (Eq, Show)

data VerilogLinkFlags = VerilogLinkFlags
    { verilogLinkCLibPath :: [String]
    , verilogLinkCLibs :: [String]
    , verilogLinkDefines :: [String]
    , verilogLinkVPath :: [String]
    , verilogLinkOFile :: String
    , verilogLinkVFlags :: [String]
    , verilogLinkLinkFlags :: [String]
    , verilogLinkUseDPI :: Bool
    , verilogLinkVsim :: Maybe String
    } deriving (Eq, Show)

data BluesimLinkFlags = BluesimLinkFlags
    { bluesimLinkOFile :: String
    , bluesimLinkCLibPath :: [String]
    , bluesimLinkCLibs :: [String]
    , bluesimLinkLinkFlags :: [String]
    , bluesimLinkCDebug :: Bool
    , bluesimLinkTimeStamps :: Bool
    } deriving (Eq, Show)

data ForeignGenFlags = ForeignGenFlags
    { foreignGenUseDPI :: Bool
    , foreignGenVPath :: [String]
    , foreignGenVdir :: Maybe String
    , foreignGenTimeStamps :: Bool
    , foreignGenShowVersion :: Bool
    } deriving (Eq, Show)

-- | Wrapper emission needs only its output directory and run observation
-- policy; foreign-link search paths and host compiler settings do not apply.
data ForeignWrapperFlags = ForeignWrapperFlags
    { foreignWrapperVdir :: Maybe String
    } deriving (Eq, Show)

internalForeignWrapperConfig :: PhaseConfig InternalFlags -> PhaseConfig ForeignWrapperFlags
internalForeignWrapperConfig config = PhaseConfig
    (phaseRunFlags config) (phaseRunOptions config)
    (ForeignWrapperFlags (internalVdir (phaseFlags config)))

verilogForeignWrapperConfig :: PhaseConfig VerilogGenFlags -> PhaseConfig ForeignWrapperFlags
verilogForeignWrapperConfig config = PhaseConfig
    (phaseRunFlags config) (phaseRunOptions config)
    (ForeignWrapperFlags (verilogGenVdir (phaseFlags config)))

foreignGenWrapperConfig :: PhaseConfig ForeignGenFlags -> PhaseConfig ForeignWrapperFlags
foreignGenWrapperConfig config = PhaseConfig
    (phaseRunFlags config) (phaseRunOptions config)
    (ForeignWrapperFlags (foreignGenVdir (phaseFlags config)))

-- | Observation helpers inspect only this phase's observation settings.
verbose :: PhaseConfig a -> Bool
verbose = (>= Verbose) . runVerbosity . phaseRunOptions

quiet :: PhaseConfig a -> Bool
quiet = (== Quiet) . runVerbosity . phaseRunOptions

extraVerbose :: PhaseConfig a -> Bool
extraVerbose = (== ExtraVerbose) . runVerbosity . phaseRunOptions

hasDump :: PhaseConfig a -> DumpFlag -> Bool
hasDump config stage = isJust (runDumpAll (phaseRunOptions config)) ||
                       hasDumpStrict config stage

hasDumpStrict :: PhaseConfig a -> DumpFlag -> Bool
hasDumpStrict config stage = isJust (lookup stage (runDumps (phaseRunOptions config)))

dumpInfo :: PhaseConfig a -> DumpFlag -> Maybe (Maybe FilePath)
dumpInfo config stage = lookup stage (runDumps options) <|> runDumpAll options
  where options = phaseRunOptions config

-- | Generated expressions share only solver policy with their enclosing phase.
-- Their language policy is explicit and independent of invocation defaults.
internalTypecheckFlags :: TypeSolverFlags -> TypecheckFlags
internalTypecheckFlags solver = TypecheckFlags
    { typecheckMaxTIStackDepth = typeSolverMaxTIStackDepth solver
    , typecheckUseProvisoSAT = typeSolverUseProvisoSAT solver
    , typecheckSatBackend = typeSolverSatBackend solver
    , typecheckAllowIncoherentMatches = False
    , typecheckLetGen = False
    }

typecheckTypeSolverFlags :: TypecheckFlags -> TypeSolverFlags
typecheckTypeSolverFlags flags = TypeSolverFlags
    { typeSolverMaxTIStackDepth = typecheckMaxTIStackDepth flags
    , typeSolverUseProvisoSAT = typecheckUseProvisoSAT flags
    , typeSolverSatBackend = typecheckSatBackend flags
    }

reduceTypeSolverFlags :: ReduceFlags -> TypeSolverFlags
reduceTypeSolverFlags flags = TypeSolverFlags
    { typeSolverMaxTIStackDepth = reduceMaxTIStackDepth flags
    , typeSolverUseProvisoSAT = reduceUseProvisoSAT flags
    , typeSolverSatBackend = reduceSatBackend flags
    }

internalTypeSolverFlags :: InternalFlags -> TypeSolverFlags
internalTypeSolverFlags flags = TypeSolverFlags
    { typeSolverMaxTIStackDepth = internalMaxTIStackDepth flags
    , typeSolverUseProvisoSAT = internalUseProvisoSAT flags
    , typeSolverSatBackend = internalSatBackend flags
    }

elabTypeSolverFlags :: ElabFlags -> TypeSolverFlags
elabTypeSolverFlags flags = TypeSolverFlags
    { typeSolverMaxTIStackDepth = elabMaxTIStackDepth flags
    , typeSolverUseProvisoSAT = elabUseProvisoSAT flags
    , typeSolverSatBackend = elabSatBackend flags
    }

-- Preserve the caller's language setting for dynamically elaborated expressions.
elabTypecheckFlags :: ElabFlags -> TypecheckFlags
elabTypecheckFlags flags = (internalTypecheckFlags (elabTypeSolverFlags flags))
    { typecheckLetGen = elabLetGen flags }
