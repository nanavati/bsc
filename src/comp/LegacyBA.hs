{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Werror -fwarn-incomplete-patterns #-}
-- Frozen f092 .ba envelope. Modern artifacts do not depend on this codec.
module LegacyBA (LegacyABin(..), legacyBAHeader) where

import Warmup ()
import ErrorUtil(internalError)
import AUses(UniqueUse(..), UseCond(..), RuleUses(..), ucTrue)
import AScheduleInfo
import BinForeignFunctions ()
import BinASyntax ()
import BinSchedule ()
import LegacyArtifactOptions (LegacyArtifactOptions(..))
import FlagTypes(DumpFlag(..), ResourceFlag(..), SATFlag(..), MsgListFlag(..), Verbosity(..))
import Verilog
import ABin
import PPrint
import BinData
import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as BC

data LegacyABin = LegacyABin
    { legacyABin :: ABin
    , legacyOptions :: Maybe LegacyArtifactOptions
    , legacyVerilog :: Maybe VProgram
    }

-- Preserve the original dumpba rendering, including the generated-Verilog
-- marker that belongs to the wire envelope rather than the neutral body.
instance PPrint LegacyABin where
    pPrint d p (LegacyABin (ABinMod modinfo version) _ vprogram) =
        text "ABin Module" $+$
        nest 2 (text "version:" <+> text version $+$
                pPrint d 0 modinfo $+$
                text "vprog:" <+> (case vprogram of
                    Nothing -> text "Nothing"
                    Just _ -> text "Just ..."))
    pPrint d p (LegacyABin abin _ _) = pPrint d p abin

legacyBAHeader :: B.ByteString
legacyBAHeader = BC.pack "bsc-ba-20260712-1"

instance Bin LegacyABin where
  writeBytes (LegacyABin (ABinForeignFunc ffinfo version) _ _) =
         section "ABinForeignFunc" $
         do -- tag which kind of module
            putI 0
            toBin version
            -- output the foreign function info
            toBin (abffi_src_name ffinfo)
            toBin (abffi_foreign_func ffinfo)
  writeBytes (LegacyABin (ABinMod modinfo version) (Just options) vprogram) =
         section "ABinMod" $
         do -- tag which kind of module
            putI 1
            toBin version
            -- output module info
            toBin (abmi_path modinfo)
            toBin (abmi_src_name modinfo)
            --toBin (abmi_time modinfo)
            toBin (abmi_apkg modinfo)
            toBin (abmi_aschedinfo modinfo)
            toBin (abmi_pps modinfo)
            toBin (abmi_oqt modinfo)
            toBin (abmi_method_dump modinfo)
            toBin (abmi_pathinfo modinfo)
            toBin options
            toBin vprogram
  writeBytes (LegacyABin (ABinModSchedErr modinfo version) (Just options) _) =
         section "ABinModSchedErr" $
         do -- tag which kind of module
            putI 2
            toBin version
            -- output module info
            toBin (abmsei_path modinfo)
            toBin (abmsei_src_name modinfo)
            toBin (abmsei_apkg modinfo)
            toBin (abmsei_aschederrinfo modinfo)
            toBin (abmsei_pps modinfo)
            toBin (abmsei_oqt modinfo)
            toBin options
  writeBytes _ = internalError "LegacyBA: module output requires legacy options"
  readBytes = do tag <- getI
                 version <- fromBin
                 case (tag) of
                   0 -> do src_name <- fromBin
                           foreign_func <- fromBin
                           let ffi = ABinForeignFuncInfo src_name foreign_func
                           return (LegacyABin (ABinForeignFunc ffi version) Nothing Nothing)
                   1 -> do path <- fromBin
                           srcName <- fromBin
                           --time <- fromBin
                           apkg <- fromBin
                           asched <- fromBin
                           pps <- fromBin
                           oqt <- fromBin
                           mi <- fromBin
                           pathinfo <- fromBin
                           flags <- fromBin
                           vprog <- fromBin
                           let modinfo =
                                   ABinModInfo path srcName apkg asched pps
                                               oqt mi pathinfo
                           return (LegacyABin (ABinMod modinfo version) (Just flags) vprog)
                   2 -> do path <- fromBin
                           srcName <- fromBin
                           apkg <- fromBin
                           aschederr <- fromBin
                           pps <- fromBin
                           oqt <- fromBin
                           flags <- fromBin
                           let modinfo =
                                   ABinModSchedErrInfo path srcName apkg
                                                       aschederr pps oqt
                           return (LegacyABin (ABinModSchedErr modinfo version) (Just flags) Nothing)
                   n -> internalError ("GenABin.Bin(ABin): tag = " ++ show n)

instance Bin AScheduleInfo where
    writeBytes (AScheduleInfo ws mumap rumap rat erdb sorder sch sgraph rrdb vsi) =
        section "AScheduleInfo" $
        do toBin ws; toBin mumap; toBin rumap; toBin rat; toBin erdb;
           toBin sorder; toBin sch; toBin sgraph; toBin rrdb; toBin vsi
    readBytes =
        do ws <- fromBin; mumap <- fromBin; rumap <- fromBin; rat <- fromBin;
           erdb <- fromBin; sorder <- fromBin; sch <- fromBin;
           sgraph <- fromBin; rrdb <- fromBin; vsi <- fromBin;
           return (AScheduleInfo ws mumap rumap rat erdb sorder sch sgraph rrdb vsi)

instance Bin AScheduleErrInfo where
    writeBytes (AScheduleErrInfo ws es mumap rumap rat erdb sorder sch sgraph rrdb vsi) =
        section "AScheduleErrInfo" $
        do toBin ws; toBin es; toBin mumap; toBin rumap; toBin rat; toBin erdb;
           toBin sorder; toBin sch; toBin sgraph; toBin rrdb; toBin vsi
    readBytes =
        do ws <- fromBin; es <- fromBin; mumap <- fromBin; rumap <- fromBin;
           rat <- fromBin; erdb <- fromBin; sorder <- fromBin; sch <- fromBin;
           sgraph <- fromBin; rrdb <- fromBin; vsi <- fromBin;
           return (AScheduleErrInfo ws es mumap rumap rat erdb sorder sch sgraph rrdb vsi)

instance Bin UniqueUse where
    writeBytes (UUAction a) = section "UUAction" $ do putI 0; toBin a
    writeBytes (UUExpr e c) = section "UUExpr" $ do putI 1; toBin e; toBin c
    readBytes =
        do i <- getI
           case i of
            0 -> do a <- fromBin; return (UUAction a)
            1 -> do e <- fromBin; c <- fromBin; return (UUExpr e c)
            n -> internalError $ "GenABin.Bin(UniqueUse).readBytes: " ++ show n

instance Bin UseCond where
    writeBytes _ = return ()
    readBytes = return ucTrue

instance Bin RuleUses where
    writeBytes (RuleUses pus rus wus) =
        section "RuleUses" $ do toBin pus; toBin rus; toBin wus
    readBytes = do pus <- fromBin; rus <- fromBin; wus <- fromBin
                   return (RuleUses pus rus wus)

instance Bin ExclusiveRulesDB where
    writeBytes erdb = section "ExclusiveRulesDB" $ toBin (erdbToList erdb)
    readBytes = do es <- fromBin; return (erdbFromList es)

instance Bin ResourceFlag where
    writeBytes RFoff    = do putI 0
    writeBytes RFsimple = do putI 1

    readBytes = do i <- getI
                   case i of
                     0 -> return RFoff
                     1 -> return RFsimple
                     n -> internalError $ "GenABin.Bin(ResourceFlag).readBytes: " ++ show n

instance {-# OVERLAPPING #-} Bin [(DumpFlag, Maybe FilePath)] where
    writeBytes _ = return ()
    readBytes    = return []

instance {-# OVERLAPPING #-} Bin (Maybe (DumpFlag, Maybe String)) where
    writeBytes _ = return ()
    readBytes    = return Nothing

instance Bin Verbosity where
    writeBytes _ = return ()
    readBytes    = return Normal

instance Bin SATFlag where
    writeBytes SAT_Yices = putI 1
    writeBytes SAT_STP = putI 2
    readBytes = do i <- getI
                   case i of
                     1 -> return SAT_Yices
                     2 -> return SAT_STP
                     n -> internalError $ "GenABin.Bin(SATFlag).readBytes: " ++ show n

instance Bin MsgListFlag where
    writeBytes AllMsgs = putI 0
    writeBytes (SomeMsgs msgs) = do putI 1; toBin msgs
    readBytes = do
      i <- getI
      case i of
        0 -> return AllMsgs
        1 -> do msgs <- fromBin; return (SomeMsgs msgs)
        n -> internalError $ "GenABin.Bin(MsgListFlag).readBytes: " ++ show n

instance Bin LegacyArtifactOptions where
    writeBytes NoLegacyArtifactOptions = internalError "LegacyBA: absent legacy options"
    writeBytes (LegacyArtifactOptions
                a_000 a_001 a_002 a_003 a_004 a_005 a_006 a_007 a_008 a_009
                a_010 a_011 a_012 a_013 a_014 a_015 a_016 a_017 a_018 a_019
                a_020 a_021 a_022 a_023 a_024 a_025 a_026 a_027 a_028 a_029
                a_030 a_031 a_032 a_033 a_034 a_035 a_036 a_037 a_038 a_039
                a_040 a_041 a_042 a_043 a_044 a_045 a_046 a_047 a_048 a_049
                a_050 a_051 a_052 a_053 a_054 a_055 a_056 a_057 a_058 a_059
                a_060 a_061 a_062 a_063 a_064 a_065 a_066 a_067 a_068 a_069
                a_070 a_071 a_072 a_073 a_074 a_075 a_076 a_077 a_078 a_079
                a_080 a_081 a_082 a_083 a_084 a_085 a_086 a_087 a_088 a_089
                a_090 a_091 a_092 a_093 a_094 a_095 a_096 a_097 a_098 a_099
                a_100 a_101 a_102 a_103 a_104 a_105 a_106 a_107 a_108 a_109
                a_110 a_111 a_112 a_113 a_114 a_115 a_116 a_117 a_118 a_119
                a_120 a_121 a_122 a_123 a_124 a_125 a_126 a_127 a_128 a_129
                a_130 a_131 a_132 a_133) =
       do wr_chunk0; wr_chunk1; wr_chunk2; wr_chunk3; wr_chunk4;
          wr_chunk5; wr_chunk6; wr_chunk7; wr_chunk8
      where
        -- The 135-field serialization is split into NOINLINE chunks so
        -- that GHC optimizes bounded pieces: compiling it as a single
        -- monadic chain needs more than 15GB of heap.
        {-# NOINLINE wr_chunk0 #-}
        wr_chunk0 =
          do toBin a_000; toBin a_001; toBin a_002; toBin a_003; toBin a_004;
             toBin a_005; toBin a_006; toBin a_007; toBin a_008; toBin a_009;
             toBin a_010; toBin a_011; toBin a_012; toBin a_013; toBin a_014
        {-# NOINLINE wr_chunk1 #-}
        wr_chunk1 =
          do toBin a_015; toBin a_016; toBin a_017; toBin a_018; toBin a_019;
             toBin a_020; toBin a_021; toBin a_022; toBin a_023; toBin a_024;
             toBin a_025; toBin a_026; toBin a_027; toBin a_028; toBin a_029
        {-# NOINLINE wr_chunk2 #-}
        wr_chunk2 =
          do toBin a_030; toBin a_031; toBin a_032; toBin a_033; toBin a_034;
             toBin a_035; toBin a_036; toBin a_037; toBin a_038; toBin a_039;
             toBin a_040; toBin a_041; toBin a_042; toBin a_043; toBin a_044
        {-# NOINLINE wr_chunk3 #-}
        wr_chunk3 =
          do toBin a_045; toBin a_046; toBin a_047; toBin a_048; toBin a_049;
             toBin a_050; toBin a_051; toBin a_052; toBin a_053; toBin a_054;
             toBin a_055; toBin a_056; toBin a_057; toBin a_058; toBin a_059
        {-# NOINLINE wr_chunk4 #-}
        wr_chunk4 =
          do toBin a_060; toBin a_061; toBin a_062; toBin a_063; toBin a_064;
             toBin a_065; toBin a_066; toBin a_067; toBin a_068; toBin a_069;
             toBin a_070; toBin a_071; toBin a_072; toBin a_073; toBin a_074
        {-# NOINLINE wr_chunk5 #-}
        wr_chunk5 =
          do toBin a_075; toBin a_076; toBin a_077; toBin a_078; toBin a_079;
             toBin a_080; toBin a_081; toBin a_082; toBin a_083; toBin a_084;
             toBin a_085; toBin a_086; toBin a_087; toBin a_088; toBin a_089
        {-# NOINLINE wr_chunk6 #-}
        wr_chunk6 =
          do toBin a_090; toBin a_091; toBin a_092; toBin a_093; toBin a_094;
             toBin a_095; toBin a_096; toBin a_097; toBin a_098; toBin a_099;
             toBin a_100; toBin a_101; toBin a_102; toBin a_103; toBin a_104
        {-# NOINLINE wr_chunk7 #-}
        wr_chunk7 =
          do toBin a_105; toBin a_106; toBin a_107; toBin a_108; toBin a_109;
             toBin a_110; toBin a_111; toBin a_112; toBin a_113; toBin a_114;
             toBin a_115; toBin a_116; toBin a_117; toBin a_118; toBin a_119
        {-# NOINLINE wr_chunk8 #-}
        wr_chunk8 =
          do toBin a_120; toBin a_121; toBin a_122; toBin a_123; toBin a_124;
             toBin a_125; toBin a_126; toBin a_127; toBin a_128; toBin a_129;
             toBin a_130; toBin a_131; toBin a_132; toBin a_133
    readBytes =
       do (a_000, a_001, a_002, a_003, a_004, a_005, a_006, a_007,
           a_008, a_009, a_010, a_011, a_012, a_013, a_014) <- rd_chunk0
          (a_015, a_016, a_017, a_018, a_019, a_020, a_021, a_022,
           a_023, a_024, a_025, a_026, a_027, a_028, a_029) <- rd_chunk1
          (a_030, a_031, a_032, a_033, a_034, a_035, a_036, a_037,
           a_038, a_039, a_040, a_041, a_042, a_043, a_044) <- rd_chunk2
          (a_045, a_046, a_047, a_048, a_049, a_050, a_051, a_052,
           a_053, a_054, a_055, a_056, a_057, a_058, a_059) <- rd_chunk3
          (a_060, a_061, a_062, a_063, a_064, a_065, a_066, a_067,
           a_068, a_069, a_070, a_071, a_072, a_073, a_074) <- rd_chunk4
          (a_075, a_076, a_077, a_078, a_079, a_080, a_081, a_082,
           a_083, a_084, a_085, a_086, a_087, a_088, a_089) <- rd_chunk5
          (a_090, a_091, a_092, a_093, a_094, a_095, a_096, a_097,
           a_098, a_099, a_100, a_101, a_102, a_103, a_104) <- rd_chunk6
          (a_105, a_106, a_107, a_108, a_109, a_110, a_111, a_112,
           a_113, a_114, a_115, a_116, a_117, a_118, a_119) <- rd_chunk7
          (a_120, a_121, a_122, a_123, a_124, a_125, a_126, a_127,
           a_128, a_129, a_130, a_131, a_132, a_133) <- rd_chunk8
          return (LegacyArtifactOptions
                a_000 a_001 a_002 a_003 a_004 a_005 a_006 a_007 a_008 a_009
                a_010 a_011 a_012 a_013 a_014 a_015 a_016 a_017 a_018 a_019
                a_020 a_021 a_022 a_023 a_024 a_025 a_026 a_027 a_028 a_029
                a_030 a_031 a_032 a_033 a_034 a_035 a_036 a_037 a_038 a_039
                a_040 a_041 a_042 a_043 a_044 a_045 a_046 a_047 a_048 a_049
                a_050 a_051 a_052 a_053 a_054 a_055 a_056 a_057 a_058 a_059
                a_060 a_061 a_062 a_063 a_064 a_065 a_066 a_067 a_068 a_069
                a_070 a_071 a_072 a_073 a_074 a_075 a_076 a_077 a_078 a_079
                a_080 a_081 a_082 a_083 a_084 a_085 a_086 a_087 a_088 a_089
                a_090 a_091 a_092 a_093 a_094 a_095 a_096 a_097 a_098 a_099
                a_100 a_101 a_102 a_103 a_104 a_105 a_106 a_107 a_108 a_109
                a_110 a_111 a_112 a_113 a_114 a_115 a_116 a_117 a_118 a_119
                a_120 a_121 a_122 a_123 a_124 a_125 a_126 a_127 a_128 a_129
                a_130 a_131 a_132 a_133)
      where
        {-# NOINLINE rd_chunk0 #-}
        rd_chunk0 =
          do a_000 <- fromBin; a_001 <- fromBin; a_002 <- fromBin; a_003 <- fromBin; a_004 <- fromBin;
             a_005 <- fromBin; a_006 <- fromBin; a_007 <- fromBin; a_008 <- fromBin; a_009 <- fromBin;
             a_010 <- fromBin; a_011 <- fromBin; a_012 <- fromBin; a_013 <- fromBin; a_014 <- fromBin
             return (a_000, a_001, a_002, a_003, a_004, a_005, a_006, a_007,
                     a_008, a_009, a_010, a_011, a_012, a_013, a_014)
        {-# NOINLINE rd_chunk1 #-}
        rd_chunk1 =
          do a_015 <- fromBin; a_016 <- fromBin; a_017 <- fromBin; a_018 <- fromBin; a_019 <- fromBin;
             a_020 <- fromBin; a_021 <- fromBin; a_022 <- fromBin; a_023 <- fromBin; a_024 <- fromBin;
             a_025 <- fromBin; a_026 <- fromBin; a_027 <- fromBin; a_028 <- fromBin; a_029 <- fromBin
             return (a_015, a_016, a_017, a_018, a_019, a_020, a_021, a_022,
                     a_023, a_024, a_025, a_026, a_027, a_028, a_029)
        {-# NOINLINE rd_chunk2 #-}
        rd_chunk2 =
          do a_030 <- fromBin; a_031 <- fromBin; a_032 <- fromBin; a_033 <- fromBin; a_034 <- fromBin;
             a_035 <- fromBin; a_036 <- fromBin; a_037 <- fromBin; a_038 <- fromBin; a_039 <- fromBin;
             a_040 <- fromBin; a_041 <- fromBin; a_042 <- fromBin; a_043 <- fromBin; a_044 <- fromBin
             return (a_030, a_031, a_032, a_033, a_034, a_035, a_036, a_037,
                     a_038, a_039, a_040, a_041, a_042, a_043, a_044)
        {-# NOINLINE rd_chunk3 #-}
        rd_chunk3 =
          do a_045 <- fromBin; a_046 <- fromBin; a_047 <- fromBin; a_048 <- fromBin; a_049 <- fromBin;
             a_050 <- fromBin; a_051 <- fromBin; a_052 <- fromBin; a_053 <- fromBin; a_054 <- fromBin;
             a_055 <- fromBin; a_056 <- fromBin; a_057 <- fromBin; a_058 <- fromBin; a_059 <- fromBin
             return (a_045, a_046, a_047, a_048, a_049, a_050, a_051, a_052,
                     a_053, a_054, a_055, a_056, a_057, a_058, a_059)
        {-# NOINLINE rd_chunk4 #-}
        rd_chunk4 =
          do a_060 <- fromBin; a_061 <- fromBin; a_062 <- fromBin; a_063 <- fromBin; a_064 <- fromBin;
             a_065 <- fromBin; a_066 <- fromBin; a_067 <- fromBin; a_068 <- fromBin; a_069 <- fromBin;
             a_070 <- fromBin; a_071 <- fromBin; a_072 <- fromBin; a_073 <- fromBin; a_074 <- fromBin
             return (a_060, a_061, a_062, a_063, a_064, a_065, a_066, a_067,
                     a_068, a_069, a_070, a_071, a_072, a_073, a_074)
        {-# NOINLINE rd_chunk5 #-}
        rd_chunk5 =
          do a_075 <- fromBin; a_076 <- fromBin; a_077 <- fromBin; a_078 <- fromBin; a_079 <- fromBin;
             a_080 <- fromBin; a_081 <- fromBin; a_082 <- fromBin; a_083 <- fromBin; a_084 <- fromBin;
             a_085 <- fromBin; a_086 <- fromBin; a_087 <- fromBin; a_088 <- fromBin; a_089 <- fromBin
             return (a_075, a_076, a_077, a_078, a_079, a_080, a_081, a_082,
                     a_083, a_084, a_085, a_086, a_087, a_088, a_089)
        {-# NOINLINE rd_chunk6 #-}
        rd_chunk6 =
          do a_090 <- fromBin; a_091 <- fromBin; a_092 <- fromBin; a_093 <- fromBin; a_094 <- fromBin;
             a_095 <- fromBin; a_096 <- fromBin; a_097 <- fromBin; a_098 <- fromBin; a_099 <- fromBin;
             a_100 <- fromBin; a_101 <- fromBin; a_102 <- fromBin; a_103 <- fromBin; a_104 <- fromBin
             return (a_090, a_091, a_092, a_093, a_094, a_095, a_096, a_097,
                     a_098, a_099, a_100, a_101, a_102, a_103, a_104)
        {-# NOINLINE rd_chunk7 #-}
        rd_chunk7 =
          do a_105 <- fromBin; a_106 <- fromBin; a_107 <- fromBin; a_108 <- fromBin; a_109 <- fromBin;
             a_110 <- fromBin; a_111 <- fromBin; a_112 <- fromBin; a_113 <- fromBin; a_114 <- fromBin;
             a_115 <- fromBin; a_116 <- fromBin; a_117 <- fromBin; a_118 <- fromBin; a_119 <- fromBin
             return (a_105, a_106, a_107, a_108, a_109, a_110, a_111, a_112,
                     a_113, a_114, a_115, a_116, a_117, a_118, a_119)
        {-# NOINLINE rd_chunk8 #-}
        rd_chunk8 =
          do a_120 <- fromBin; a_121 <- fromBin; a_122 <- fromBin; a_123 <- fromBin; a_124 <- fromBin;
             a_125 <- fromBin; a_126 <- fromBin; a_127 <- fromBin; a_128 <- fromBin; a_129 <- fromBin;
             a_130 <- fromBin; a_131 <- fromBin; a_132 <- fromBin; a_133 <- fromBin
             return (a_120, a_121, a_122, a_123, a_124, a_125, a_126, a_127,
                     a_128, a_129, a_130, a_131, a_132, a_133)

instance Bin VProgram where
    writeBytes (VProgram ms dpis c) = do toBin ms; toBin dpis; toBin c
    readBytes = do ms <- fromBin; dpis <- fromBin; c <- fromBin; return (VProgram ms dpis c)

instance Bin VModule where
    writeBytes (VModule name c ports body) =
        do toBin name; toBin c; toBin ports; toBin body
    readBytes = do name <- fromBin; c <- fromBin; ports <- fromBin;
                   body <-fromBin; return (VModule name c ports body)

instance Bin VDPI where
    writeBytes (VDPI name ret args) =
        do toBin name; toBin ret; toBin args
    readBytes = do name <- fromBin; ret <- fromBin; args <- fromBin;
                   return (VDPI name ret args)

instance Bin VDPIType where
    writeBytes (VDT_void)    = do putI 0
    writeBytes (VDT_byte)    = do putI 1
    writeBytes (VDT_int)     = do putI 2
    writeBytes (VDT_longint) = do putI 3
    writeBytes (VDT_wide n)  = do putI 4; toBin n
    writeBytes (VDT_string)  = do putI 5
    writeBytes (VDT_poly)    = do putI 6
    readBytes = do
      i <- getI
      case i of
        0 -> return VDT_void
        1 -> return VDT_byte
        2 -> return VDT_int
        3 -> return VDT_longint
        4 -> do n <- fromBin; return (VDT_wide n)
        5 -> return VDT_string
        6 -> return VDT_poly
        n -> internalError $ "GenABin(VArg).readBytes: " ++ show n

instance Bin VId where
    writeBytes (VId s i m) = do toBin s; toBin i; toBin m
    readBytes = do s <- fromBin; i <- fromBin; m <- fromBin;
                   return (VId s i m)

instance Bin VArg where
    writeBytes (VAInput i r)       = do putI 0; toBin i; toBin r
    writeBytes (VAInout i i' r)    = do putI 1; toBin i; toBin i'; toBin r
    writeBytes (VAOutput i r)      = do putI 2; toBin i; toBin r
    writeBytes (VAParameter i r d) = do putI 3; toBin i; toBin r; toBin d
    readBytes = do
      i <- getI
      case i of
        0 -> do i <- fromBin; r <- fromBin; return (VAInput i r)
        1 -> do i <- fromBin; i' <- fromBin; r <- fromBin;
                return (VAInout i i' r)
        2 -> do i <- fromBin; r <- fromBin; return (VAOutput i r)
        3 -> do i <- fromBin; r <- fromBin; d <- fromBin;
                return (VAParameter i r d)
        n -> internalError $ "GenABin(VArg).readBytes: " ++ show n

instance Bin VExpr where
    writeBytes (VEConst n)        = do putI 0; toBin n
    writeBytes (VEReal n)         = do putI 1; toBin n
    writeBytes (VEWConst i w b v) = do putI 2; toBin i; toBin w; toBin b;
                                       toBin v
    writeBytes (VEUnknown n s)    = do putI 3; toBin n; toBin s
    writeBytes (VEString s)       = do putI 4; toBin s
    writeBytes (VETriConst ts)    = do putI 5; toBin ts
    writeBytes (VEUnOp i o e)     = do putI 6; toBin i; toBin o; toBin e
    writeBytes (VEOp i e1 o e2)   = do putI 7; toBin i; toBin e1; toBin o;
                                       toBin e2
    writeBytes (VEVar i)          = do putI 8; toBin i
    writeBytes (VEConcat es)      = do putI 9; toBin es
    writeBytes (VEIndex i e)      = do putI 10; toBin i; toBin e
    writeBytes (VESelect e hi lo) = do putI 11; toBin e; toBin hi; toBin lo
    writeBytes (VESelect1 e n)    = do putI 12; toBin e; toBin n
    writeBytes (VERepeat e n)     = do putI 13; toBin e; toBin n
    writeBytes (VEIf c t f)       = do putI 14; toBin c; toBin t; toBin f
    writeBytes (VEFctCall i es)   = do putI 15; toBin i; toBin es
    writeBytes (VEMacro m)        = do putI 16; toBin m;
    readBytes = do
      i <- getI
      case i of
        0 -> do n <- fromBin; return (VEConst n)
        1 -> do n <- fromBin; return (VEReal n)
        2 -> do i <- fromBin; w <- fromBin; b <- fromBin; v <- fromBin;
                return (VEWConst i w b v)
        3 -> do n <- fromBin; s <- fromBin; return (VEUnknown n s)
        4 -> do s <- fromBin; return (VEString s)
        5 -> do ts <- fromBin; return (VETriConst ts)
        6 -> do i <- fromBin; o <- fromBin; e <- fromBin; return (VEUnOp i o e)
        7 -> do i <- fromBin; e1 <- fromBin; o <- fromBin; e2 <- fromBin;
                return (VEOp i e1 o e2)
        8 -> do i <- fromBin; return (VEVar i)
        9 -> do es <- fromBin; return (VEConcat es)
        10 -> do i <- fromBin; e <- fromBin; return (VEIndex i e)
        11 -> do e <- fromBin; hi <- fromBin; lo <- fromBin;
                 return (VESelect e hi lo)
        12 -> do e <- fromBin; n <- fromBin; return (VESelect1 e n)
        13 -> do e <- fromBin; n <- fromBin; return (VERepeat e n)
        14 -> do c <- fromBin; t <- fromBin; f <- fromBin; return (VEIf c t f)
        15 -> do i <- fromBin; es <- fromBin; return (VEFctCall i es)
        16 -> do m <- fromBin;  return (VEMacro m);
        n -> internalError $ "GenABin(VExpr).readBytes: " ++ show n

instance Bin VTri where
    writeBytes v = toBin (fromEnum v)
    readBytes = fromBin >>= return . toEnum

instance Bin VOp where
    writeBytes v = toBin (fromEnum v)
    readBytes = fromBin >>= return . toEnum

instance Bin VMItem where
    writeBytes (VMDecl d)           = do putI 0; toBin d
    writeBytes (VMInst m i pas pos) = do putI 1; toBin m; toBin i; toBin pas;
                                         toBin pos
    writeBytes (VMAssign lv e)      = do putI 2; toBin lv; toBin e
    writeBytes (VMStmt a body)      = do putI 3; toBin a; toBin body
    writeBytes (VMComment c m)      = do putI 4; toBin c; toBin m
    writeBytes (VMRegGroup i s c m) = do putI 5; toBin i; toBin s; toBin c;
                                         toBin m
    writeBytes (VMGroup a body)     = do putI 6; toBin a; toBin body
    writeBytes (VMFunction f)       = do putI 7; toBin f
    readBytes = do
      i <- getI
      case i of
        0 -> do d <- fromBin; return (VMDecl d)
        1 -> do m <- fromBin; i <- fromBin; pas <- fromBin; pos <- fromBin;
                return (VMInst m i pas pos)
        2 -> do lv <- fromBin; e <- fromBin; return (VMAssign lv e)
        3 -> do a <- fromBin; body <- fromBin; return (VMStmt a body)
        4 -> do c <- fromBin; m <- fromBin; return (VMComment c m)
        5 -> do i <- fromBin; s <- fromBin; c <- fromBin; m <- fromBin;
                return (VMRegGroup i s c m)
        6 -> do a <- fromBin; body <- fromBin; return (VMGroup a body)
        7 -> do f <- fromBin; return (VMFunction f)
        n -> internalError $ "GenABin(VMItem).readBytes: " ++ show n

instance Bin VVDecl where
    writeBytes (VVDecl t r vs) = do putI 0; toBin t; toBin r; toBin vs
    writeBytes (VVDWire r v e) = do putI 1; toBin r; toBin v; toBin e
    readBytes = do
      i <- getI
      case i of
        0 -> do t <- fromBin; r <- fromBin; vs <- fromBin;
                return (VVDecl t r vs)
        1 -> do r <- fromBin; v <- fromBin; e <- fromBin;
                return (VVDWire r v e)
        n -> internalError $ "GenABin(VVDecl).readBytes: " ++ show n

instance Bin VDType where
    writeBytes t = toBin (fromEnum t)
    readBytes = fromBin >>= return . toEnum

instance Bin VVar where
    writeBytes (VVar i)     = do putI 0; toBin i
    writeBytes (VArray r i) = do putI 1; toBin r; toBin i
    readBytes = do
      i <- getI
      case i of
        0 -> do i <- fromBin; return (VVar i)
        1 -> do r <- fromBin; i <- fromBin; return (VArray r i)
        n -> internalError $ "GenABin(VVar).readBytes: " ++ show n

instance Bin VLValue where
    writeBytes (VLId i)      = do putI 0; toBin i
    writeBytes (VLConcat vs) = do putI 1; toBin vs
    writeBytes (VLSub v e)   = do putI 2; toBin v; toBin e
    readBytes = do
      i <- getI
      case i of
        0 -> do i <- fromBin; return (VLId i)
        1 -> do vs <- fromBin; return (VLConcat vs)
        2 -> do v <- fromBin; e <- fromBin; return (VLSub v e)
        n -> internalError $ "GenABin(VLValue).readBytes: " ++ show n

instance Bin VStmt where
    writeBytes (VAt e s)         = do putI 0; toBin e; toBin s
    writeBytes (Valways s)       = do putI 1; toBin s
    writeBytes (Vinitial s)      = do putI 2; toBin s
    writeBytes (VSeq ss)         = do putI 3; toBin ss
    writeBytes (Vcasex e as p f) = do putI 4; toBin e; toBin as; toBin p;
                                      toBin f
    writeBytes (Vcase e as p f)  = do putI 5; toBin e; toBin as; toBin p;
                                      toBin f
    writeBytes (VAssign lv e)    = do putI 6; toBin lv; toBin e
    writeBytes (VAssignA lv e)   = do putI 7; toBin lv; toBin e
    writeBytes (Vif c t)         = do putI 8; toBin c; toBin t
    writeBytes (Vifelse c t f)   = do putI 9; toBin c; toBin t; toBin f
    writeBytes (Vdumpvars n is)  = do putI 10; toBin n; toBin is
    writeBytes (VTask i es)      = do putI 11; toBin i; toBin es
    writeBytes (VAssert e es)    = do putI 12; toBin e; toBin es
    writeBytes (VZeroDelay)      = do putI 13
    readBytes = do
      i <- getI
      case i of
        0 -> do e <- fromBin; s <- fromBin; return (VAt e s)
        1 -> do s <- fromBin; return (Valways s)
        2 -> do s <- fromBin; return (Vinitial s)
        3 -> do ss <- fromBin; return (VSeq ss)
        4 -> do e <- fromBin; as <- fromBin; p <- fromBin; f <- fromBin;
                return (Vcasex e as p f)
        5 -> do e <- fromBin; as <- fromBin; p <- fromBin; f <- fromBin;
                return (Vcase e as p f)
        6 -> do lv <- fromBin; e <- fromBin; return (VAssign lv e)
        7 -> do lv <- fromBin; e <- fromBin; return (VAssignA lv e)
        8 -> do c <- fromBin; t <- fromBin; return (Vif c t)
        9 -> do c <- fromBin; t <- fromBin; f <- fromBin; return (Vifelse c t f)
        10 -> do n <- fromBin; is <- fromBin; return (Vdumpvars n is)
        11 -> do i <- fromBin; es <- fromBin; return (VTask i es)
        12 -> do e <- fromBin; es <- fromBin; return (VAssert e es)
        13 -> return VZeroDelay
        n -> internalError $ "GenABin(VStmt).readBytes: " ++ show n

instance Bin VEventExpr where
    writeBytes (VEEOr e1 e2)  = do putI 0; toBin e1; toBin e2
    writeBytes (VEEposedge e) = do putI 1; toBin e
    writeBytes (VEEnegedge e) = do putI 2; toBin e
    writeBytes (VEE e)        = do putI 3; toBin e
    writeBytes (VEEMacro s e) = do putI 4; toBin s; toBin e
    readBytes = do
      i <- getI
      case i of
        0 -> do e1 <- fromBin; e2 <- fromBin; return (VEEOr e1 e2)
        1 -> do e <- fromBin; return (VEEposedge e)
        2 -> do e <- fromBin; return (VEEnegedge e)
        3 -> do e <- fromBin; return (VEE e)
        4 -> do s <- fromBin; e <- fromBin; return (VEEMacro s e)
        n -> internalError $ "GenABin(VEventExpr).readBytes: " ++ show n

instance Bin VCaseArm where
    writeBytes (VCaseArm es s) = do putI 0; toBin es; toBin s
    writeBytes (VDefault s)    = do putI 1; toBin s
    readBytes = do
      i <- getI
      case i of
        0 -> do es <- fromBin; s <- fromBin; return (VCaseArm es s)
        1 -> do s <- fromBin; return (VDefault s)
        n -> internalError $ "GenABin(VCaseArm).readBytes: " ++ show n

instance Bin VFunction where
    writeBytes (VFunction i r d s) = do toBin i; toBin r; toBin d; toBin s
    readBytes = do i <- fromBin; r <- fromBin; d <- fromBin; s <- fromBin;
                   return (VFunction i r d s)
