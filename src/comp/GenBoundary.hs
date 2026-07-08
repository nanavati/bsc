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
import System.Environment(lookupEnv)
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
import BoundaryDesc(BoundaryEntryR(..))
import GenWrap(BoundarySpec(..), GWMonad, GenState(..),
               runGWMonadNoFail, runGWMonadGetNoFail,
               chkInterface, flatTypeId,
               isClockType, isResetType, isParamType,
               isInoutType, isVectorType,
               genFromBody, genFromBodyDesc, mkArgPortTypes,
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
--
-- The first argument is the module's parsed boundary_ description,
-- when one was found and -boundary-fold asked for it (increments
-- 7-8): the interface-rendering body is then built from the
-- description's entries (see GenWrap.genFromBodyDesc) instead of
-- re-walking the pragma tables.  Nothing, or any disagreement with
-- the interface inventory, takes the legacy path silently.
renderWrapperCDefn :: Maybe [BoundaryEntryR a] -> BoundarySpec -> DefFun
renderWrapperCDefn mentries spec pps fmod wire_info sch pathinfo ips symt fields true_ifc_ids = do
  let
      iprags = bs_iprags spec
      i = bs_id spec
      (ts, tr) = case getArrows (bs_qt spec) of
                   (ats, TAp _ r) -> (ats, r)
                   _ -> internalError "GenBoundary.renderWrapperCDefn: ts, tr"
      st1 = (bs_state spec) { symtable = symt }
  -- do not use ifc prags here
  -- the flat type's identity is a GenWrap-time fact: pragmas that
  -- arrive later (contract-derived always_ready) change ports, never
  -- the nominal type (renderings do not fork types)
  (st2, ti_) <- runGWMonadGetNoFail (flatTypeId (bs_pps spec) tr) st1
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
  -- the fold (increments 7-8): when the boundary_ description is in
  -- hand, build the interface-rendering body from its entries -- the
  -- description-directed walk consumes them in emission order,
  -- checking agreement with the interface inventory at every leaf;
  -- any disagreement renders by the legacy walk instead
  let entryLeaf (BFieldR { bf_path = p, bf_slots = ss }) = (p, ss)
      entryLeaf (BOpaqueR { bo_path = p, bo_slots = ss }) = (p, ss)
  mfold <- case mentries of
             Nothing -> return Nothing
             Just entries ->
                 runGWMonadNoFail
                     (genFromBodyDesc (map entryLeaf entries)
                          arg_pts vlift true_ifc_ids ti_ finfs)
                     st4
  -- instrumentation: when BSC_BOUNDARY_FOLD_LOG names a file, record
  -- the per-module fold-vs-fallback decision there (only meaningful
  -- when a description was supplied, i.e. under -boundary-fold)
  case mentries of
    Nothing -> return ()
    Just _ -> do
      mlog <- lookupEnv "BSC_BOUNDARY_FOLD_LOG"
      case mlog of
        Nothing -> return ()
        Just fn -> let what = maybe "fallback" (const "fold") mfold
                   in  appendFile fn (what ++ " " ++
                                      getIdBaseString i ++ "\n")
  body <- case mfold of
            Just b -> return b
            Nothing ->
                runGWMonadNoFail
                    (genFromBody arg_pts vlift true_ifc_ids ti_ ifcId finfs)
                    st4
  let cls = CClause (map CPVar vs) [] body
  return $ CValueSign (CDef i (bs_cqt spec) [cls])

-- ==============================
