{-# LANGUAGE CPP #-}
{-# OPTIONS_GHC -fwarn-name-shadowing #-}
module GenBoundary(
                   DefFun,
                   renderWrapperCDefn
                  ) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import Control.Monad(zipWithM)
import PFPrint
import Position(noPosition)
import Error(internalError)
import Id
import PreIds
import CSyntax
import CSyntaxUtil
import SymTab(SymTab)
import CType(getArrows)
import VModInfo(VSchedInfo, VPathInfo, VFieldInfo, VWireInfo, VPort)
import Pragma
import GenWrap(BoundarySpec(..), GWMonad, GenState(..),
               runGWMonadNoFail, runGWMonadGetNoFail,
               chkInterface, flatTypeId,
               isClockType, isResetType, isParamType,
               isInoutType, isVectorType,
               genFromBody, mkArgPortTypes,
               isRdyToRemoveField, fixupVeriField,
               ePack, ePrimInoutCast0)

-- ==============================
-- Rendering the final wrapper

-- This is the final wrapper computation, at the end of synthesis:
-- once the back end has computed the schedule, wire and path
-- information for a module, the wrapper definition (which converts
-- between the bitified signals and the abstract values) is assembled
-- from that information and the BoundarySpec recorded by GenWrap.
-- This code used to be a continuation ("DefFun") which GenWrap
-- captured in a closure; it is now a top-level function so that the
-- module pragmas are an explicit argument (allowing pragmas
-- synthesized after GenWrap to be supplied) and the remaining inputs
-- are pure data.

type DefFun = [PProp] -> Bool -> VWireInfo -> VSchedInfo -> VPathInfo ->
              [VPort] -> SymTab -> [VFieldInfo] -> [Id] ->
              IO CDefn

-- The [PProp] argument is the module's pragmas (the pragmas from the
-- ifc declaration are per-type facts, recorded in the BoundarySpec).
-- XXX: alwaysEnabled is dropped and broken (not propagated to {inhigh})
renderWrapperCDefn :: BoundarySpec -> DefFun
renderWrapperCDefn spec pps fmod wire_info sch pathinfo ips symt fields true_ifc_ids = do
  let
      iprags = bs_iprags spec
      i = bs_id spec
      (ts, tr) = case getArrows (bs_qt spec) of
                   (ats, TAp _ r) -> (ats, r)
                   _ -> internalError "GenBoundary.renderWrapperCDefn: ts, tr"
      st1 = (bs_state spec) { symtable = symt }
  -- do not use ifc prags here
  (st2, ti_) <- runGWMonadGetNoFail (flatTypeId pps tr) st1
  let vs =  take (length ts) tmpVarIds
  (st3, Just (ifcId, _, finfs)) <- runGWMonadGetNoFail (chkInterface tr) st2
  let
      -- return an expression for creating the arg (from the wrapper's args)
      -- and the type of the internal module's arg (for port-type saving)
      genArg :: CExpr -> Type -> GWMonad [(CExpr, CType)]
      genArg vexpr t =
       do
         --traceM( "In genArg: " ++ ppReadable v ++ " " ++ ppReadable t ) ;
         cint <- chkInterface t
         case cint of
           Just x -> -- interface arguments are not supported and should
                     -- already have generated an error
                     internalError ("renderWrapperCDefn: ifc arg: " ++
                                    ppReadable (t,x))
           Nothing -> do
             isInout <- isInoutType t
             case isInout of
              Just _ -> return [(CApply ePrimInoutCast0 [vexpr], t)]
              _ ->
               do
                 isClock <- isClockType t
                 isReset <- isResetType t
                 isParam <- isParamType t
                 if (isClock || isReset || isParam)
                   then return [(vexpr,t)]
                   else do isVector <- isVectorType t
                           case isVector of
                             Just (n,tVec,_) -> genVecArg vexpr n tVec
                             _ -> return [(CApply ePack [vexpr], t)]
      genVecArg :: CExpr -> Integer -> Type -> GWMonad [(CExpr, CType)]
      genVecArg vexpr sz tVec = do
         -- make the expression for each port
         let nums = [0..(sz-1)]
             primselect = idPrimSelectFn noPosition
             lit k = CLit $ num_to_cliteral_at noPosition k
             selector n = cVApply primselect [posLiteral noPosition,
                                              vexpr, lit n]
             elem_sels = map selector nums
         elem_exprs <- mapM (`genArg` tVec) elem_sels
         return (concat elem_exprs)

  (st4, argss) <- runGWMonadGetNoFail (zipWithM genArg (map CVar vs) ts) st3
  let (arg_exprs, arg_ts) = unzip $ concat argss
      -- make the arg port-types, for saving in the module
      arg_pts = mkArgPortTypes wire_info arg_ts
  let
      fields' = filter (not . (isRdyToRemoveField (iprags ++ pps))) fields
      veriFields = (map (fixupVeriField (iprags ++ pps) ips) fields')
      vexp = xWrapperModuleVerilog
             fmod
             pps
             (CLit(CLiteral noPosition(LString( getIdBaseString i) )))
             wire_info
             arg_exprs
             veriFields
             sch
             pathinfo
      vlift = (cVApply idLiftModule [vexp])
  body <- runGWMonadNoFail
              (genFromBody arg_pts vlift true_ifc_ids ti_ ifcId finfs)
              st4
  let cls = CClause (map CPVar vs) [] body
  return $ CValueSign (CDef i (bs_cqt spec) [cls])

-- ==============================
