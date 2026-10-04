-- | Shared option enums. Invocation-wide Flags belongs to the driver.
module FlagTypes
    ( Verbosity(..), DumpFlag(..), ResourceFlag(..), SATFlag(..), MsgListFlag(..) ) where


import Warmup ()
data Verbosity = Quiet | Normal | Verbose | ExtraVerbose
   deriving(Eq, Show, Ord, Enum)

data DumpFlag
        =
        -- Bluespec source file
          DFdepend
        | DFcpp
        | DFvpp
        | DFbsvlex
        | DFparsed
        | DFimports
        | DFopparse
        | DFsyminitial
        | DFsympostgenwrap
        | DFsympostderiving
        | DFsympostctxreduce
        | DFsympostbinary
        | DFgenfuncwrap
        | DFgenwrap
        | DFderiving
        | DFctxreduce
        | DFconvinst
        | DFtypecheck
        | DFgenforeign
        | DFgenVPI
        | DFsimplified
        | DFinternal
        | DFbinary
        | DFfixup
        | DFisimplify
        | DFwriteBin

        -- module generation
        | DFexpanded
        | DFinlineFmt
        | DFinline
        | DFtransform
        | DFsplitIf
        | DFlift
        | DFiparams
        | DFidroprules
        | DFATS
        | DFATSexpand
        | DFdumpLambdaCalculus
        | DFdumpSAL
        | DFATSperfspec
        | DFATSsplice
        | DFATSclean
        | DFpathsPreSched
        | DFschedule
        | DFresources
        | DFvschedinfo
        | DFscheduledefs
        | DFdumpschedule
        | DFcheckproofs
        | DFpathsPostSched
        | DFnoinline
        | DFaddSchedAssumps
        | DFremoveAssumps
        | DFdropundet
        | DFwriteABin
        | DFwrappergen
        | DFwrappercomp

        -- Wrapper compilation phases
        | DFwrapper_ctxreduce
        | DFwrapper_typecheck
        | DFwrapper_simplified
        | DFwrapper_internal
        | DFwrapper_fixup

        -- Generate Verilog
        | DFforeignMap
        | DFastate
        | DFrwire
        | DFcreg
        | DFrenameio
        | DFadropdefs
        | DFaopt
        | DFsynthesize
        | DFveriquirks
        | DFfinalcleanup
        | DFIOproperties
        | DFverilog
        | DFverilogDollar
        | DFwriteVerilog

        -- Link
        | DFreadelab

        -- Link Verilog
        | DFcompileVPI
        | DFveriloglink

        -- Generate/Link Bluesim
        | DFsimExpand
        | DFsimDepend
        | DFsimPackageOpt
        | DFsimMakeCBlocks
        | DFsimCOpt
        | DFsimBlocksToC
        | DFgenSystemC
        | DFwriteC
        | DFbluesimcompile
        | DFbluesimlink

        deriving (Eq, Read, Show, Enum, Bounded)

data ResourceFlag
       = RFoff    -- don't reschedule: fail if not enough resources
       | RFsimple -- reschedule: arbitrate resources (drop first edge in graph)
       deriving (Eq, Show)

data SATFlag
       = SAT_Yices
       | SAT_STP
       deriving (Eq, Show)

data MsgListFlag = AllMsgs | SomeMsgs [String]
                 deriving (Show, Eq)

