{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Werror -fwarn-incomplete-patterns #-}
-- Baseline ASyntax codecs shared by module artifacts and legacy .ba.
-- Field order and representation are unchanged from GenABin.
module BinASyntax () where

import Warmup ()
import ErrorUtil(internalError)
import Backend
import Wires
import ASyntax
import InstNodes(InstNode(..))
import BinData

instance Bin APackage where
    writeBytes (APackage {
               apkg_name = mi,
               apkg_is_wrapped = is_wrap,
               apkg_backend = be,
               apkg_size_params = ps,
               apkg_inputs = inps,
               apkg_clock_domains = clks,
               apkg_external_wires = wi,
               apkg_external_wire_types = wpt,
               apkg_reset_list = rsts,
               apkg_state_instances = avis,
               apkg_local_defs = ds,
               apkg_rules = rs,
               apkg_schedule_pragmas = asps,
               apkg_interface = aifcs,
               apkg_inst_comments = ics,
               apkg_inst_tree = inst_tree,
               apkg_proof_obligations = pos
           }) = if (null pos)
                then section "APackage" $
                     do toBin mi
                        toBin is_wrap
                        toBin be
                        toBin ps
                        toBin inps
                        toBin clks
                        toBin wi
                        toBin wpt
                        toBin rsts
                        toBin avis
                        toBin ds
                        toBin rs
                        toBin asps
                        toBin aifcs
                        toBin inst_tree
                        toBin ics
                        -- proof obligations not written
                else internalError $ "GenABin.Bin(APackage).readBytes: non-empty proof obligations"
    readBytes = do mi <- fromBin
                   is_wrap <- fromBin
                   be <- fromBin
                   ps <- fromBin
                   inps <- fromBin
                   clks <- fromBin
                   wi <- fromBin
                   wpt <- fromBin
                   rsts <- fromBin
                   avis <- fromBin
                   ds <- fromBin
                   rs <- fromBin
                   asps <- fromBin
                   aifcs <- fromBin
                   inst_tree <- fromBin
                   ics <- fromBin
                   return (APackage {
                             apkg_name = mi,
                             apkg_is_wrapped = is_wrap,
                             apkg_backend = be,
                             apkg_size_params = ps,
                             apkg_inputs = inps,
                             apkg_clock_domains = clks,
                             apkg_external_wires = wi,
                             apkg_external_wire_types = wpt,
                             apkg_reset_list = rsts,
                             apkg_state_instances = avis,
                             apkg_local_defs = ds,
                             apkg_rules = rs,
                             apkg_schedule_pragmas = asps,
                             apkg_interface = aifcs,
                             apkg_inst_comments = ics,
                             apkg_inst_tree = inst_tree,
                             apkg_proof_obligations = []
                                    })

instance Bin Backend where
    writeBytes (Bluesim) = putI 0
    writeBytes (Verilog) = putI 1
    readBytes = do
        i <- getI
        case i of
         0 -> return Bluesim
         1 -> return Verilog
         n -> internalError $ "GenABin.Bin(Backend).readBytes: " ++ show n

instance Bin AAbstractInput where
    writeBytes (AAI_Port p) = do putI 0; toBin p
    writeBytes (AAI_Clock osc mgate) = do putI 1; toBin osc; toBin mgate
    writeBytes (AAI_Reset r) = do putI 2; toBin r
    writeBytes (AAI_Inout r n) = do putI 3; toBin r; toBin n
    readBytes = do
        i <- getI
        case i of
         0 -> do p <- fromBin; return (AAI_Port p)
         1 -> do osc <- fromBin; mgate <- fromBin; return (AAI_Clock osc mgate)
         2 -> do r <- fromBin; return (AAI_Reset r)
         3 -> do r <- fromBin; n <- fromBin; return (AAI_Inout r n)
         n -> internalError $ "GenABin.Bin(AAbstractInfo).readBytes: " ++ show n

instance Bin AVInst where
    writeBytes (AVInst i t ui ms pts vmi ias iarr) =
        section "AVInst" $
        do toBin i; toBin t; toBin ui; toBin ms; toBin pts;
           toBin vmi; toBin ias; toBin iarr
    readBytes = do i <- fromBin; t <- fromBin; ui <- fromBin; ms <- fromBin;
                   pts <- fromBin; vmi <- fromBin; ias <- fromBin; iarr <- fromBin;
                   return (AVInst i t ui ms pts vmi ias iarr)

instance Bin ARule where
    writeBytes (ARule i ps d wps pred act asmps mp) =
        section "ARule" $
        do toBin i; toBin ps; toBin d; toBin wps; toBin pred; toBin act;
           toBin asmps; toBin mp
    readBytes =
        do i <- fromBin; ps <- fromBin; d <- fromBin; wps <- fromBin;
           pred <- fromBin; act <- fromBin; asmps <- fromBin; mp <- fromBin;
           return (ARule i ps d wps pred act asmps mp)

instance Bin AAssumption where
    writeBytes (AAssumption p as) = do toBin p; toBin as
    readBytes = do p <- fromBin; as <- fromBin;
                   return (AAssumption p as)

instance Bin AAction where
    writeBytes (ACall i m as) = do putI 0; toBin i; toBin m; toBin as
    writeBytes (AFCall i f isC as isA) =
        do putI 1; toBin i; toBin f; toBin isC; toBin as; toBin isA
    writeBytes (ATaskAction i f isC c as tmp ty isA) =
        do putI 2; toBin i; toBin f; toBin isC; toBin c; toBin as;
           toBin tmp; toBin ty; toBin isA
    readBytes =
        do i <- getI
           case i of
            0 -> do i <- fromBin; m <- fromBin; as <- fromBin;
                    return (ACall i m as)
            1 -> do i <- fromBin; f <- fromBin; isC <- fromBin; as <- fromBin;
                    isA <- fromBin; return (AFCall i f isC as isA)
            2 -> do i <- fromBin; f <- fromBin; isC <- fromBin; c <- fromBin;
                    as <- fromBin; tmp <- fromBin; ty <- fromBin;
                    isA <- fromBin;
                    return (ATaskAction i f isC c as tmp ty isA)
            n -> internalError $ "GenABin.Bin(AAction).readBytes: " ++ show n

instance Bin WireProps where
    writeBytes (WireProps cd rs) = do toBin cd; toBin rs
    readBytes = do cd <- fromBin; rs <- fromBin; return (WireProps cd rs)

instance Bin AIFace where
    writeBytes (AIDef name is ps pred val vfi asmps) =
        do putI 0; toBin name; toBin is; toBin ps; toBin pred; toBin val;
           toBin vfi; toBin asmps
    writeBytes (AIAction is ps pred name body vfi) =
        do putI 1; toBin is; toBin ps; toBin pred; toBin name; toBin body;
           toBin vfi
    writeBytes (AIActionValue is ps pred name body val vfi) =
        do putI 2; toBin is; toBin ps; toBin pred; toBin name; toBin body;
           toBin val; toBin vfi
    writeBytes (AIClock name clk vfi) =
        do putI 3; toBin name; toBin clk; toBin vfi
    writeBytes (AIReset name rst vfi) =
        do putI 4; toBin name; toBin rst; toBin vfi
    writeBytes (AIInout name iot vfi) =
        do putI 5; toBin name; toBin iot; toBin vfi
    readBytes =
        do i <- getI
           case i of
            0 -> do name <- fromBin; is <- fromBin; ps <- fromBin;
                    pred <- fromBin; val <- fromBin; vfi <- fromBin;
                    asmps <- fromBin;
                    return (AIDef name is ps pred val vfi asmps)
            1 -> do is <- fromBin; ps <- fromBin; pred <- fromBin;
                    name <- fromBin; body <- fromBin; vfi <- fromBin;
                    return (AIAction is ps pred name body vfi)
            2 -> do is <- fromBin; ps <- fromBin; pred <- fromBin;
                    name <- fromBin; body <- fromBin; val <- fromBin;
                    vfi <- fromBin;
                    return (AIActionValue is ps pred name body val vfi)
            3 -> do name <- fromBin; clk <- fromBin; vfi <- fromBin;
                    return (AIClock name clk vfi)
            4 -> do name <- fromBin; rst <- fromBin; vfi <- fromBin;
                    return (AIReset name rst vfi)
            5 -> do name <- fromBin; iot <- fromBin; vfi <- fromBin;
                    return (AIInout name iot vfi)
            n -> internalError $ "GenABin.Bin(AIFace).readBytes: " ++ show n

instance Bin InstNode where
  writeBytes (StateVar i) = do
    putI 0; toBin i
  writeBytes (Rule i) = do
    putI 1; toBin i
  writeBytes (Loc name ctype ignore ignore_name un children) = do
    putI 2; toBin name; toBin ctype;
    toBin ignore; toBin ignore_name; toBin un; toBin children
  readBytes = do
    i <- getI
    case i of
      0 -> do i <- fromBin; return (StateVar i)
      1 -> do i <- fromBin; return (Rule i)
      2 -> do name <- fromBin; ctype <- fromBin;
              ignore <- fromBin; ignore_name <- fromBin;
              un <- fromBin; children <- fromBin;
              return (Loc name ctype ignore ignore_name un children)
      n -> internalError ("GenABin.Bin(InstNode) - tag: " ++ show n)
