-- | Foreign function uses in the Verilog netlist.
module VerilogForeignFunctions(getForeignFunctions) where
import ASyntax
import ASyntaxUtil
import AVerilogSyntax
import AVerilogSyntaxUtil ()
import ForeignFunctions(ForeignFuncMap, ForeignFunction)
import qualified Data.Map as M
import Data.List(nub)
import Data.Maybe(mapMaybe)

getForeignFunctions :: ForeignFuncMap -> ASPackage -> [ForeignFunction]
getForeignFunctions ffmap aspkg =
  let
      expr_ff_uses = findAExprs exprForeignCalls aspkg
      expr_ff_names =
        [ i | (AFunCall { ae_funname = i, ae_isC = True }) <- expr_ff_uses ]

      act_ff_uses = concatMap snd (aspkg_foreign_calls aspkg)
      act_ff_names = map afc_fun act_ff_uses

      ff_names = nub (expr_ff_names ++ act_ff_names)

      findFF name = M.lookup name ffmap
  in
      mapMaybe findFF ff_names

