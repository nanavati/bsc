-- | Validation specific to the Verilog netlist after state lowering.
module AVerilogCheck(aSMCheck, aSignalCheck, aSMethCheck) where

import Warmup ()
import AVerilogSyntax(ASPackage(..))
import ASyntax
import ASyntaxUtil
import ACheck(chkAVInst, chkADef, chkAForeignBlock, tracePP)
import ErrorUtil(internalError)
import PPrint
import qualified Data.Set as S
import Data.List(foldl')

-- type check the state elements, definitions and foreign function calls
-- scheduled package
aSMCheck :: ASPackage -> Bool
aSMCheck asp =
        all chkAVInst (aspkg_state_instances asp)
        && all chkADef (aspkg_values asp)
        && all chkADef (aspkg_inout_values asp)
        && all chkAForeignBlock (aspkg_foreign_calls asp)
        && chkDupWires asp
        -- XXX when module parameters carry an expr for default value,
        -- XXX check that here

-- make sure a wire is never defined twice in an ASPackage
chkDupWires :: ASPackage -> Bool
chkDupWires asp = tracePP "chkDupWires" dup_set (S.null dup_set)
  where (dup_set, _) = foldl' step_sets (S.empty, S.empty) all_names
        step_sets (dup_set, name_set) i | i `S.member` name_set = (S.insert i dup_set, name_set)
                                        | otherwise = (dup_set, S.insert i name_set)
        def_names  = [ i | ADef i _ _ _ <- aspkg_values asp ]
        state_outs = map fst (aspkg_state_outputs asp)
        params     = map fst (aspkg_parameters asp)
        inputs     = map fst (aspkg_inputs asp)
        inouts     = map fst (aspkg_inouts asp)
        all_names  = def_names ++ state_outs ++ params ++ inputs ++ inouts

------
-- Check that the names used in expression are all defined.
--
-- Available names:
--   ps = instantiation parameters
--   is = module inputs (clk, rst, method arguments, imported interface port)
--   ds = defined signals
--   souts = signal names created to attach to submodule ports
-- Expressions:
--   insts = expressions to instantiation
--   ds = expressions defining signals
--   fs = foreign function calls
--
-- Returns any names that are used but not defined.
--
aSignalCheck :: ASPackage -> [AId]
aSignalCheck (ASPackage _ fmod ps _ is ios insts souts ds iods fs _ _ _) =
    let
        pnames = [ i | (i,_) <- ps ]
        inames = [ i | (i,_) <- is ]
        ionames= [ i | (i,_) <- ios ]
        dnames = [ i | ADef i _ _ _ <- ds ]
        snames = [ i | (i,_) <- souts ]

        -- used in ASDef
        defs = dnames
        -- used in ASPort
        ports = inames ++ snames ++ ionames
        -- used in ASParam
        params = pnames

        -- XXX if parameters carried expressions for their default values,
        -- XXX we would check those uses here

        iexprs = concatMap avi_iargs insts
        dexprs = [ e | ADef i _ e _ <- ds ]
        iodexprs = [ e | ADef i _ e _ <- iods ]
        fexprs = concat [ clks ++ es ++ rsts | (clks, fcalls) <- fs,
                                               AForeignCall _ _ es _ rsts <- fcalls ]

        exprs = fexprs ++ iexprs ++ dexprs ++ iodexprs
        -- build set from the list
        defSet   = S.fromList defs
        portSet  = S.fromList ports
        paramSet = S.fromList params

    in
        checkUses defSet portSet paramSet exprs


-- return The list of all names not referenced in the given environments
checkUses :: S.Set AId -> S.Set AId -> S.Set AId -> [AExpr] -> [AId]
checkUses ds is ps es = concatMap (checkUse ds is ps) es

checkUse :: S.Set AId -> S.Set AId -> S.Set AId -> AExpr -> [AId]
checkUse ds is ps (APrim _ _ _ es)     = checkUses ds is ps es
checkUse ds is ps (AMethCall _ i m es) = checkUses ds is ps es  -- XXX check i and m ?
checkUse ds is ps (AMethValue _ i m)   = [] -- XXX check i and m ?
checkUse ds is ps (ATuple _ es)        = checkUses ds is ps es
checkUse ds is ps (ATupleSel _ e _)    = checkUse ds is ps e
checkUse ds is ps (ANoInlineFunCall _ _ _ es) = checkUses ds is ps es
checkUse ds is ps (AFunCall { ae_args = es }) = checkUses ds is ps es
-- because all of the expressions used are used by the ATaskAction
checkUse ds is ps (ATaskValue { })     = []
checkUse ds is ps (ASPort _ i)         = if (S.member i is) then [] else [i]
checkUse ds is ps (ASParam _ i)        = if (S.member i ps) then [] else [i]
checkUse ds is ps (ASDef _ i)          = if (S.member i ds) then [] else [i]
checkUse ds is ps (ASInt _ _ _)        = []
checkUse ds is ps (ASReal _ _ _)       = []
checkUse ds is ps (ASStr _ _ _)        = []
checkUse ds is ps (ASAny _ Nothing)    = []
checkUse ds is ps (ASAny _ (Just e))   = internalError ("aSignalCheck surviving ASAny: " ++ ppReadable e)
checkUse ds is ps (ASClock _ (AClock { aclock_osc = osc, aclock_gate = gate})) =
                                       (checkUse ds is ps osc) ++ (checkUse ds is ps gate)
checkUse ds is ps (ASReset _ (AReset { areset_wire = wire })) =
                                       checkUse ds is ps wire
checkUse ds is ps (ASInout _ (AInout { ainout_wire = wire })) =
                                       checkUse ds is ps wire
checkUse ds is ps (AMGate _ i c) = []  -- XXX check i and c ?

------

-- After aState, method calls should all have been converted to port
-- connections to submodules.  AMethCall and AMethValue should not
-- exist in the ASPackage.  Task and foreign function calls can still
-- exist.

-- AMOsc, AMGate, AMReset should also have been converted to port
-- connections.

aSMethCheck :: ASPackage -> Bool
aSMethCheck (ASPackage _ _ _ _ _ _ ss _ ds iods fs _ _ _) =
    all chkMethAVInst ss  &&
    all chkMethADef ds    &&
    all chkMethADef iods  &&
    all chkMethAForeignBlock fs


chkMethAExpr :: AExpr -> Bool
chkMethAExpr e@(AMethCall { }) =
    internalError ("chkMethAExpr: methcall " ++ ppReadable e)
chkMethAExpr e@(AMethValue { }) =
    internalError ("chkMethAExpr: methvalue " ++ ppReadable e)
chkMethAExpr e@(AMGate { }) =
    internalError ("chkMethAExpr: mgate " ++ ppReadable e)
chkMethAExpr (APrim _ _ _ es) = all chkMethAExpr es
chkMethAExpr (AFunCall { ae_args = es }) = all chkMethAExpr es
chkMethAExpr (ATaskValue { }) = True
-- Others don't have arguments to recurse
chkMethAExpr _ = True

-- Check the expressions in defs
chkMethADef :: ADef -> Bool
chkMethADef (ADef _ _ e _) = chkMethAExpr e

-- Check the expressions in instantiations
chkMethAVInst :: AVInst -> Bool
chkMethAVInst aa =
    all chkMethAExpr (getPorts aa) &&
    all chkMethAExpr (getInouts aa) &&
    all chkMethAExpr (getClocks aa) &&
    all chkMethAExpr (getResets aa)

-- Check the expressions in foreign blocks
chkMethAForeignBlock :: AForeignBlock -> Bool
chkMethAForeignBlock (clks, fcalls) = all chkMethAForeignCall fcalls

chkMethAForeignCall :: AForeignCall -> Bool
chkMethAForeignCall (AForeignCall _ _ es _ rsts) =
    all chkMethAExpr (es ++ rsts)
