-- | Elaboration-time primitive template for optional runtime conflict checks.
module ACFTemplate (getCFConditionWireTemplate) where
import Warmup ()
import CSyntax
import SymTab
import TypeCheck (topExpr)
import Type
import qualified TIMonad as TIM (TIResult(..), runTI)
import PhaseConfig
import IConv (iConvExpr)
import ASyntax
import ASyntaxUtil
import ISyntax
import ISyntaxUtil hiding (noReset)
import IExpandUtils (HExpr, HeapData)
import IExpand (iExpand)
import ISplitIf (iSplitIf)
import AConv (aConv)
import PreIds
import qualified Data.Map as M
import PPrint
import Error (internalError, ErrorHandle)

getCFConditionWireTemplate :: ErrorHandle -> PhaseConfig ElabFlags -> SymTab ->
                             M.Map AId HExpr -> APackage -> IO (Maybe AVInst)
getCFConditionWireTemplate errh flags symtab definitions apkg
    | needsCFConditionWires apkg = Just <$> getRWireInstTemplate errh flags symtab definitions
    | otherwise = pure Nothing

getRWireInstTemplate :: ErrorHandle -> PhaseConfig ElabFlags -> SymTab ->
                  M.Map AId HExpr -> IO AVInst
getRWireInstTemplate errh flags r alldefs = do
  let blobT = TAp tModule tEmpty
  case TIM.tiResult $ (TIM.runTI (elabTypecheckFlags (phaseFlags flags)) False r (topExpr blobT (CVar id__mkRWireSubmodule))) of
    Left errs -> internalError (ppReadable errs)
    Right (_,e') -> do
      let iexpr = iConvExpr errh (elabTypeSolverFlags (phaseFlags flags)) r alldefs e'
      let def :: IDef HeapData
          def = IDef id_x (iGetType iexpr) iexpr []
      let flags' = flags { phaseRunOptions = (phaseRunOptions flags) { runShowElabProgress = False } }
      iepkg <- iExpand errh flags' r alldefs M.empty False [] def
      rwire_pkg <- aConv errh [] flags (iSplitIf flags iepkg)
      case (apkg_state_instances rwire_pkg) of
        [rwire_inst] ->
          let params = take 1 (avi_iargs rwire_inst) ++ [nullClock, noReset]
              rwire_inst' = rwire_inst { avi_iargs = params }
          in return rwire_inst'
        is -> internalError ("getRWireBlob: " ++ ppReadable is)

-- | A clock that never ticks but is always ready
nullClock :: AExpr
nullClock = ASClock aTClock (AClock aFalse aTrue)

noReset :: AExpr
noReset = aNoReset

