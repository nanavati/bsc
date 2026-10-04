-- | Traversal and diagnostic instances for the Verilog netlist.
module AVerilogSyntaxUtil () where

import Prelude hiding ((<>))
import Warmup ()
import AVerilogSyntax(ASPackage(..))
import ASyntaxUtil(AExprs(..))
import TopUtils(Stats(..), showLen)
import PPrint
import IdPrint(ppId)

instance AExprs ASPackage where
    mapAExprs f pkg@(ASPackage { aspkg_state_instances = vs,
                                aspkg_values = defs,
                                aspkg_inout_values = iodefs,
                                aspkg_foreign_calls = fs })
        = pkg { aspkg_state_instances = (mapAExprs f vs),
                aspkg_values = (mapAExprs f defs),
                aspkg_inout_values = (mapAExprs f iodefs),
                aspkg_foreign_calls = (mapAExprs f fs) }
    -- monadic
    mapMAExprs f pkg@(ASPackage { aspkg_state_instances = vs,
                                  aspkg_values = defs,
                                  aspkg_inout_values = iodefs,
                                  aspkg_foreign_calls = fs })
        = do vs' <- mapMAExprs f vs
             defs' <- mapMAExprs f defs
             iodefs' <- mapMAExprs f iodefs
             fs' <- mapMAExprs f fs
             return (pkg { aspkg_state_instances = vs',
                           aspkg_values = defs',
                           aspkg_inout_values = iodefs',
                           aspkg_foreign_calls = fs' })
    -- find
    findAExprs f pkg@(ASPackage { aspkg_state_instances = vs,
                                aspkg_values = defs,
                                aspkg_inout_values = iodefs,
                                aspkg_foreign_calls = fs })
        = findAExprs f vs ++ findAExprs f defs ++
          findAExprs f iodefs ++ findAExprs f fs

instance Stats ASPackage where
    pStats _ (ASPackage i _ _ os is ios vs sos ds _ fs _ _ _) =
        (text "module" <+> ppId PDReadable i) $+$
        (text "  " <> (
        showLen os "outputs" $+$
        showLen is "inputs" $+$
        showLen ios "inouts" $+$
        showLen vs "state elements" $+$
        showLen sos "state elements outputs" $+$
        showLen ds "local definitions" $+$
        showLen fs "foreign function calls"))

