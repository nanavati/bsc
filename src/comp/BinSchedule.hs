{-# OPTIONS_GHC -Werror -fwarn-incomplete-patterns #-}
-- Baseline schedule-data codecs, independent of scheduler algorithms.
module BinSchedule () where

import Warmup ()
import ErrorUtil(internalError)
import StaticSchedule (ASchedule(..), AScheduler(..))
import AUses (MethodId(..))
import AScheduleInfo
import ADumpScheduleInfo (RuleConflictType)
import BinData
import BinASyntax ()
import qualified Data.Set as S
import qualified Data.Map as M

instance Bin ASchedule where
    writeBytes (ASchedule ss order) = section "ASchedule" $ do toBin ss; toBin order
    readBytes = do ss <- fromBin; order <- fromBin; return (ASchedule ss order)

instance Bin AScheduler where
    writeBytes (ASchedEsposito cs) = toBin cs
    readBytes = do cs <- fromBin; return (ASchedEsposito cs)

instance Bin MethodId where
    writeBytes (MethodId i m) = section "MethodId" $ do toBin i; toBin m
    readBytes = do i <- fromBin; m <- fromBin; return (MethodId i m)

instance Bin RuleRelationDB where
    writeBytes (RuleRelationDB dset cmap) =
        section "RuleRelationDB" $ do toBin (S.toList dset)
                                      toBin (M.toList cmap)
    readBytes = do dset_list <- fromBin
                   cmap_list <- fromBin
                   let dset = S.fromList dset_list
                       cmap = M.fromList cmap_list
                   return (RuleRelationDB dset cmap)

instance Bin RuleRelationInfo where
    writeBytes (RuleRelationInfo mCF mSC mRes mCycle mPragma mArb) =
        do toBin mCF; toBin mSC; toBin mRes; toBin mCycle; toBin mPragma;
           toBin mArb
    readBytes =
        do mCF <- fromBin; mSC <- fromBin; mRes <- fromBin;
           mCycle <- fromBin; mPragma <- fromBin; mArb <- fromBin;
           return (RuleRelationInfo mCF mSC mRes mCycle mPragma mArb)

instance Bin Conflicts where
    writeBytes (CUse mms)              = do putI 0; toBin mms
    writeBytes (CCycle rs)             = do putI 1; toBin rs
    writeBytes (CMethodsBeforeRules)   = do putI 2
    writeBytes (CUserEarliness pos)    = do putI 3; toBin pos
    writeBytes (CUserAttribute pos)    = do putI 4; toBin pos
    writeBytes (CUserPreempt pos)      = do putI 5; toBin pos
    writeBytes (CResource m)           = do putI 6; toBin m
    writeBytes (CArbitraryChoice)      = do putI 7
    writeBytes (CFFuncArbitraryChoice) = do putI 8
    readBytes =
        do i <- getI
           case i of
            0 -> do mms <- fromBin; return (CUse mms)
            1 -> do rs <- fromBin; return (CCycle rs)
            2 -> return CMethodsBeforeRules
            3 -> do pos <- fromBin; return (CUserEarliness pos)
            4 -> do pos <- fromBin; return (CUserAttribute pos)
            5 -> do pos <- fromBin; return (CUserPreempt pos)
            6 -> do m <- fromBin; return (CResource m)
            7 -> return CArbitraryChoice
            8 -> return CFFuncArbitraryChoice
            n -> internalError $ "GenABin.Bin(Conflicts).readBytes: " ++ show n

instance Bin SchedNode where
    writeBytes (Sched i) = section "SchedNode" $ do putI 0; toBin i
    writeBytes (Exec i)  = section "SchedNode" $ do putI 1; toBin i
    readBytes =
        do i <- getI
           case i of
            0 -> do i <- fromBin; return (Sched i)
            1 -> do i <- fromBin; return (Exec i)
            n -> internalError $ "GenABin.Bin(SchedNode).readBytes: " ++ show n

instance Bin RuleConflictType where
    writeBytes rct = toBin (fromEnum rct)
    readBytes = fromBin >>= return . toEnum
