-- | Verilog netlist representation after rule and interface lowering.
-- These records describe physical signals and instances; scheduled semantic
-- modules remain in ASModule and do not depend on this representation.
module AVerilogSyntax
    ( ASPackage(..)
    , ASPSignalInfo(..)
    , ASPMethodInfo(..)
    , ASPCommentInfo(..)
    ) where

import Prelude hiding ((<>))
import Warmup ()
import ASyntax
    ( AId, AType, AInput, AOutput, AVInst, AStateOut, ADef, AForeignBlock )
import Eval
import Id (Id)
import IdPrint (ppId)
import PPrint

data ASPackage = ASPackage {
        -- package name
         aspkg_name :: AId,
        -- module wrapped around a pure function with pragma no-inline
        aspkg_is_wrapped :: Bool,
        -- parameters (names in Verilog)
        -- (i.e. module args generated as params, size parameters)
        -- XXX there are no size parameters because we don't support
        -- XXX synthesis of size-polymorphic modules
        aspkg_parameters :: [AInput],
        -- package outputs (output clocks/resets, method results/RDY)
        aspkg_outputs :: [AOutput],
        -- package inputs (input clocks/resets, method args/EN, module args)
        -- (i.e. clock, reset, method arguments, module args as ports)
        aspkg_inputs :: [AInput],
        -- package inouts (module args and provided interface)
        aspkg_inouts :: [AInput],
        -- state elements (Verilog instances)
        aspkg_state_instances :: [AVInst],
        -- state element outputs (wires coming out of state elements)
        aspkg_state_outputs :: [AStateOut],
        -- defs (all sorts)
        aspkg_values :: [ADef],
        -- inout defs
        aspkg_inout_values :: [ADef],
        -- foreign function calls (grouped by clock domain)
        aspkg_foreign_calls :: [AForeignBlock],
        -- wire ports from inlined submodules (RWire and CReg)
        --   which shouldn't be unecessarily inlined away
        aspkg_inlined_ports :: [AId],
        -- info about which Ids are for what purpose
        aspkg_signal_info :: ASPSignalInfo,
        -- user comments to be included in the output RTL
        aspkg_comment_info :: ASPCommentInfo
    }
        deriving (Eq, Show)

instance NFData ASPackage where
    rnf (ASPackage n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14) =
        rnf14 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 n13 n14

data ASPSignalInfo = ASPSignalInfo {
        -- input params, ports, clocks, and resets are all in one list
        -- (can use isParam etc to filter it out)
        aspsi_inputs :: [AId],
        -- the interface output clocks (and possibly empty list of gates)
        aspsi_output_clks :: [(AId,[AId])],
        aspsi_output_rsts :: [AId],
        aspsi_ifc_iots :: [AId],
        -- the ifc methods
        aspsi_methods :: [ASPMethodInfo],

        -- inline submodule info (RWire and CReg)
        -- XXX this somewhat duplicates the aspkg_inlined_ports field
        --   * instance name
        --   * module name as String
        --   * list of ports that became signals
        aspsi_inlined_ports :: [(AId, String, [AId])],

        -- rule scheduling signals
        --   relation from rule name to its CAN_FIRE and WILL_FIRE signals
        aspsi_rule_sched :: [(AId, [AId])],

        -- mux selectors
        --   ids of defs created in AState for the selectors to submod muxes
        aspsi_mux_selectors :: [AId],
        -- mux values
        --   ids of defs created in AState for the values to submod muxes
        aspsi_mux_values :: [AId],
        -- submodule enables
        --   ids of defs created in AState for the enables to submod methods
        aspsi_submod_enables :: [AId]
    }
        deriving (Eq, Show)


instance PPrint ASPSignalInfo where
    pPrint d p aspsi = text "ASPSignalInfo = " <> braces
                       (text "Inputs" <+> pPrint d p (aspsi_inputs aspsi)
                       $+$ text "Output Clocks" <+> pPrint d p (aspsi_output_clks aspsi)
                       $+$ text "Output Resets" <+> pPrint d p (aspsi_output_rsts aspsi)
                       $+$ text "Inouts" <+> pPrint d p (aspsi_ifc_iots aspsi)
                       $+$ text "Methods" <+> pPrint d p (aspsi_methods aspsi)
                       -- $+$ text "Inlined Ports" <+> pPrint d p (aspsi_inlined_ports aspsi)
                       )

        --   relation from method name to
        --     type of method (value, action, actionvalue) as string
        --     ports for RDY, EN, val, args
        --     names of the associated rules (for methods with actions)
data ASPMethodInfo = ASPMethodInfo {
                                    aspm_name :: AId,
                                    aspm_type :: String,
                                    aspm_mrdyid :: Maybe AId,
                                    aspm_menableid :: Maybe AId,
                                    aspm_resultids :: [AId],
                                    aspm_inputs :: [AId],
                                    aspm_assocrules :: [AId]
                                                       }
                   deriving (Eq, Show)

instance PPrint ASPMethodInfo where
    pPrint d p aspmi = text "method:" <+> pPrint d p( aspm_name aspmi)
                       <+> text (aspm_type aspmi) <> equals <>
                       braces ( pPrint d 0 (aspm_mrdyid aspmi) <+>
                                pPrint d 0 (aspm_menableid aspmi) <+>
                                pPrint d 0 (aspm_resultids aspmi) $+$
                                pPrint d 0 (aspm_inputs aspmi) $+$
                                pPrint d 0 (aspm_assocrules aspmi) )

instance NFData ASPMethodInfo where
    rnf (ASPMethodInfo n t mr me mres ins assoc) = rnf7 n t mr me mres ins assoc

instance NFData ASPSignalInfo where
    rnf (ASPSignalInfo ins oclks orsts iots meths iports rsched muxsels muxvals senables) =
        rnf10 ins oclks orsts iots meths iports rsched muxsels muxvals senables

data ASPCommentInfo = ASPCommentInfo {
        -- comments on submodule instantiations
        aspci_submod_insts :: [(Id, [String])],
        -- comments on rules
        aspci_rules :: [(AId, [String])]
        -- comments on methods
        -- aspsi_methods :: ...
    }
        deriving (Eq, Show)

instance NFData ASPCommentInfo where
    rnf (ASPCommentInfo insts rules) = rnf2 insts rules

ppV :: PDetail -> (AId, AType) -> Doc
ppV d (i, t) = pPrint d 0 i <+> text "::" <+> pPrint d 0 t <> text ";"

-- parallel rule groups; total order on state
-- (first rule in the list writes, present only if there are state conflicts)
instance PPrint ASPackage where
    pPrint d p pack@(ASPackage mi fmod ps exps is ios ss sos ds iods fs ws ids cmap) =
        (text "ASPackage" <+> ppId d mi <> if fmod then text " -- function" else text "") $+$
        text "-- ASPackage parameters" $+$
        (text "" <+> sep (map (pPrint d 0) ps) <> text ";") $+$
        text "-- ASPackage outputs" $+$
        (text "" <+> sep (map (pPrint d 0) exps) <> text ";") $+$
        text "-- ASPackage inputs" $+$
        foldr (($+$) . ppV d) (text "") is $+$
        text "-- ASPackage inouts" $+$
        foldr (($+$) . ppV d) (text "") ios $+$
        text "-- ASP state elements" $+$
        foldr (($+$) . pPrint d 0) (text "") ss $+$
        text "-- ASP state elements outputs" $+$
        foldr (($+$) . ppV d) (text "") sos $+$
        text "-- ASP inlined rwire ports" $+$
        foldr (($+$) . pPrint d 0) (text "") ws $+$
        text "-- ASP definitions" $+$
        foldr (($+$) . pPrint d 0) (text "") ds $+$
        text "-- ASP inout definitions" $+$
        foldr (($+$) . pPrint d 0) (text "") iods $+$
        text "-- ASP foreign function calls" $+$
        foldr (($+$) . pPrint d 0) (text "") fs $+$
        text "--ASP Signal Info" $+$ pPrint d 0 (aspkg_signal_info pack)
