module ACheck(aMCheck, chkAVInst, chkADef, chkAForeignBlock, tracePP) where

import Util(allSame)
import PPrint
import IntLit
import ErrorUtil(internalError)
import Prim
import ASyntax
import ASyntaxUtil
import Params(isConstAExpr)
import Data.Maybe(isNothing)
import Data.List(genericLength)
import PreIds(idInout_)
import Debug.Trace

-- type check the the state elements, definitions, rules and interface
aMCheck :: APackage -> Bool
aMCheck apkg =
        all chkAVInst (apkg_state_instances apkg)
        && all chkADef (apkg_local_defs apkg)
        && all chkARule (apkg_rules apkg)
        && all chkAIface (apkg_interface apkg)

        -- XXX when module parameters carry an expr for default value,
        -- XXX check that here

        -- XXX if we wanted, we could check that the port list and
        -- XXX the VArgInfo at the top-level agree on types
        -- XXX (e.g., clock to clock, reset to reset)


-----

chkAVInst :: AVInst -> Bool
chkAVInst aa =
  let
      chkParam e = let t = chkAExpr e
                   in  isConstAExpr [] e && (isBit t || isString t || isReal t)
  in
    (tracePP "chkAVInst Params" aa $ all chkParam (getParams aa)) &&
    (tracePP "chkAVInst Ports"  aa $ all (isBitOrInout_ . chkAExpr) (getPorts aa)) &&
    (tracePP "chkAVInst Clocks" aa $ all (isClock . chkAExpr) (getClocks aa)) &&
    (tracePP "chkAVInst Resets" aa $ all (isReset . chkAExpr) (getResets aa)) &&
    (tracePP "chkAVInst Inouts" aa $ all (isInout_ . chkAExpr) (getInouts aa))


chkADef :: ADef -> Bool
chkADef aa@(ADef _ t e _) =
    let et = chkAExpr e
    in if t == et
        then True
        else internalError ("chkADef "
                ++ ppReadable aa
                ++ ": (" ++ show aa ++ ") "
                ++ ppReadable t ++ " /= " ++ ppReadable et)

chkARule :: ARule -> Bool
chkARule aa@(ARule _ _ _ _ p as asmps _) =
    tracePP "chkARule" aa $ chkAExpr p == aTBool && all chkAAction as && all chkAAssumption asmps

chkAAssumption :: AAssumption -> Bool
chkAAssumption aa@(AAssumption p as) =
    tracePP "chkAAssumption" aa $ chkAExpr p == aTBool && all chkAAction as

chkAIface :: AIFace -> Bool
chkAIface aa@(AIDef { aif_value = d,
                      aif_assumps = asmps  }) =
    tracePP "chkAIface AIDef" aa $ chkADef d && all chkAAssumption asmps

chkAIface aa@(AIAction { aif_body = rs }) =
    tracePP "chkAIface AIAction" aa $ all chkARule rs

chkAIface aa@(AIActionValue { aif_value = d, aif_body = rs }) =
    tracePP "chkAIface AIActionValue" aa $ (all chkARule rs) && (chkADef d)

chkAIface aa@(AIClock { aif_clock = c }) =
    tracePP "chkAIface AIClock" aa $ chkAClock c

chkAIface aa@(AIReset { aif_reset = r }) =
    tracePP "chkAIface AIReset" aa $ chkAReset r

chkAIface aa@(AIInout { aif_inout = r }) =
    tracePP "chkAIface AIInout" aa $ chkAInout r

chkCond :: AType -> Bool
chkCond = isBit1

-- A method argument must either be a Bit-typed expression (a single
-- hardware input port) or an ATuple of Bit-typed elements (one per
-- hardware input port, for SplitPorts arguments).
chkMethArg :: AExpr -> Bool
chkMethArg e = case chkAExpr e of
                 ATTuple ts -> all isBit ts
                 t          -> isBit t

chkAAction :: AAction -> Bool
chkAAction aa@(ACall i m (c:es)) =
    tracePP "chkAAction ACall" aa $
        all chkMethArg es && chkCond (chkAExpr c)
chkAAction afc@(AFCall { aact_objid = i, aact_args = (c:es) }) =
    tracePP "chkAAction AFCall" afc $
        chkCond (chkAExpr c) && all (isForeignArg . chkAExpr) es
chkAAction ata@(ATaskAction { aact_args = (c:es) }) =
    tracePP "chkAAction ATaskAction" ata $
        chkCond (chkAExpr c) && all (isForeignArg . chkAExpr) es
chkAAction _ = False

chkAForeignBlock :: AForeignBlock -> Bool
chkAForeignBlock (clks, fcalls) = all chkAForeignCall fcalls

chkAForeignCall :: AForeignCall -> Bool
chkAForeignCall afc@(AForeignCall id fun (c:es) _ _) =
    tracePP "chkAForeignCall" afc $ (chkCond (chkAExpr c)) && all (isForeignArg . chkAExpr) es
chkAForeignCall afc = False

chkAExpr :: AExpr -> AType
chkAExpr e@(APrim _ t PrimMul es) =
        let ts = map chkAExpr es
            -- getBit (ATBit n) = n
            -- getBit _ = internalError("ACheck checkAExpr.getBit" ++ (show e))
        -- multiplication can widen or narrow the result
        in  if all isBit ts && isBit t  -- && sum (map getBit ts) == getBit t
            then
                t
            else
                internalError ("chkAExpr * : " ++ ppReadable e)
chkAExpr e@(APrim _ t PrimQuot es) =
        let ts = map chkAExpr es
            getBit (ATBit n) = n
            getBit _ = internalError("ACheck checkAExpr.getBit" ++ (show e))
        in  if all isBit ts && isBit t && (getBit t == getBit (ts!!0))
            then
                t
            else
                internalError ("chkAExpr * : " ++ ppReadable e)
chkAExpr e@(APrim _ t PrimRem es) =
        let ts = map chkAExpr es
            getBit (ATBit n) = n
            getBit _ = internalError("ACheck checkAExpr.getBit" ++ (show e))
        in  if all isBit ts && isBit t && (getBit t == getBit (ts!!1))
            then
                t
            else
                internalError ("chkAExpr * : " ++ ppReadable e)
chkAExpr e@(APrim _ t PrimConcat es) =
        let ts = map chkAExpr es
            getBit (ATBit n) = n
            getBit _ = internalError("ACheck checkAExpr.getBit" ++ (show e))
        in  if all isBit ts && isBit t && sum (map getBit ts) == getBit t
            then
                t
            else
                if not (isBit t) then internalError ("chkAExpr ++: result not bit type (" ++ ppString t ++ "): " ++ ppReadable e)
                else if not (all isBit ts) then internalError ("chkAExpr ++: some args not bit type (" ++ ppString ts ++ "): " ++ ppReadable e)
                else internalError ("chkAExpr ++: expression bitsize (" ++ ppString (getBit t) ++ ") does not match sum of args bitsizes (" ++ ppString (sum (map getBit ts)) ++ ") from (" ++ ppString ts ++ "): " ++ ppReadable e)
chkAExpr e@(APrim _ t op es) | isRelOp op =
        let ts = map chkAExpr es
        in  if t == aTBool && all isBit ts && allSame ts
                then t
                else internalError ("chkAExpr: relop " ++ ppReadable (e, t, ts))
chkAExpr e@(APrim _ t op [v]) | op == PrimSignExt || op == PrimZeroExt =
        case (chkAExpr v, t) of
        (ATBit n, ATBit m) | n <= m -> t
        _ -> internalError ("chkAExpr: " ++ ppReadable (e, chkAExpr v, t))
chkAExpr e@(APrim _ t PrimIf (c:es)) =
    if all ((compatTypesWthStr t) . chkAExpr) es && chkAExpr c == aTBool
    then t
    else internalError ("chkAExpr: if " ++ ppReadable (e, t))
chkAExpr e@(APrim _ t op es) | op == PrimPriMux || op == PrimMux =
        if f es
                then t
                else internalError ("chkAExpr: mux " ++ ppReadable t ++ ppReadable e)
  where f [] = True
        f (c:x:xs) = chkAExpr c == aTBool && compatTypesWthStr (chkAExpr x)  t && f xs
        f _ = internalError "chkAExpr mux"
-- XXX could check a little more
chkAExpr e@(APrim _ t PrimCase (x:v:ces)) =
        if compatTypesWthStr (chkAExpr v) t && chk ces
                then t
                else internalError ("chkAExpr: case " ++ ppReadable e)
  where chk [] = True
        chk (c:e:ces) = chkAExpr c == te && compatTypesWthStr (chkAExpr e) t && chk ces
        chk _ = False
        te = chkAExpr x


chkAExpr e@(APrim _ t PrimExtract es) =
        if all (isBit . chkAExpr) es
                then t
                else internalError ("chkAExpr: extract " ++ ppReadable e)
chkAExpr e@(APrim _ t op [e1, e2]) | isShift op =
        if chkAExpr e1 == t {- XXX && chkAExpr e2 == aTNat-}
                then t
                else internalError ("chkAExpr: shift " ++ ppReadable e)

chkAExpr e@(APrim _ arr_ty PrimBuildArray elem_es) =
    case arr_ty of
      ATArray sz elem_ty ->
          if (genericLength elem_es /= sz)
          then internalError ("chkAExpr: array size: " ++ ppReadable e)
          else if all ((compatTypesWthStr elem_ty) . chkAExpr) elem_es
               then arr_ty
               else internalError ("chkAExpr: array elems: " ++ ppReadable e ++
                                   ppReadable elem_ty ++
                                   ppReadable (map chkAExpr elem_es))
      _ -> internalError ("chkAExpr: array type: " ++ ppReadable (arr_ty, e))
chkAExpr e@(APrim _ ret_ty PrimArrayDynSelect es) =
  let err = internalError ("chkAExpr: array select: " ++ ppReadable e)
  in  case es of
        [arr_e, idx_e] ->
            case (chkAExpr arr_e) of
              (ATArray sz elem_ty) ->
                  if ((compatTypesWthStr ret_ty elem_ty) &&
                      isBit (chkAExpr idx_e))
                  then ret_ty
                  else err
              _ -> err
        _ -> err
chkAExpr e@(APrim _ ret_ty PrimArrayDynUpdate es) =
  -- These should not exist after IExpand
  internalError ("chkAExpr: array update: " ++ ppReadable e)
{-
  let err = internalError ("chkAExpr: array update: " ++ ppReadable e)
  in  case es of
        [arr_e, idx_e, val_e] ->
            case (chkAExpr arr_e) of
              arr_ty@(ATArray sz elem_ty) ->
                  if ((compatTypesWthStr ret_ty arr_ty) &&
                      (compatTypesWthStr elem_ty (chkAExpr val_e)) &&
                      isBit (chkAExpr idx_e))
                  then ret_ty
                  else err
              _ -> err
        _ -> err
-}

chkAExpr e@(APrim _ t PrimStringConcat es)
   | all isStringType (t : map chkAExpr es) = t
   | otherwise = internalError ("chkAExpr: string prim " ++ ppReadable (e, t, map chkAExpr es))

-- all other primitives
chkAExpr e@(APrim _ t op es) =
        if all ((== t) . chkAExpr) es
                then t
                else internalError ("chkAExpr: other " ++ ppReadable (e, t, map chkAExpr es))

chkAExpr e@(AMethCall t _ _ es) =
        if all chkMethArg es
                then t
                else internalError ("chkAExpr: methcall " ++ ppReadable e)
chkAExpr e@(AFunCall { ae_type = t, ae_args = es }) =
        if all (isForeignArg . chkAExpr) es
                then t
                else internalError ("chkAExpr: funcall " ++ ppReadable e)

chkAExpr (ASInt _ _ (IntLit _ _ i)) | i < 0 =
        internalError ("chkAExpr: negative constant: " ++ show i)
chkAExpr (ASInt _ t@(ATBit sz) (IntLit _ _ i)) =
        -- check that "log2(i+1) <= sz"
        -- or, in otherwords, "2^sz >  i"
        if (2^sz > i)
        then t
        else internalError ("chkAExpr: integer does not fit in size: " ++
                            ppReadable (i,sz))
chkAExpr (ASInt _ t (IntLit _ _ i)) =
        internalError ("chkAExpr: non-bit integer: " ++ ppReadable (t,i))

chkAExpr e@(ASClock t c) =
         if chkAClock c
           then t
           else internalError ("chkAExpr: invalid clock: " ++ ppReadable e)

chkAExpr e@(ASReset t r) =
        if chkAReset r
           then t
           else internalError ("chkAExpr: invalid reset: " ++ ppReadable e)

chkAExpr e@(ASInout t r) =
        if chkAInout r
           then t
           else internalError ("chkAExpr: invalid inout: " ++ show e)

chkAExpr e@(AMGate t _ _) =
        if isBit1 t
        then t
        else internalError ("chkAExpr: invalid clock gate: " ++ ppReadable e)

chkAExpr e = aType e

chkAClock :: AClock -> Bool
chkAClock (AClock { aclock_osc = osc, aclock_gate = gate }) = isBit1 (aType osc) && isBit1 (aType gate)

chkAReset :: AReset -> Bool
chkAReset (AReset { areset_wire = wire }) = isBit1 (aType wire)

chkAInout :: AInout -> Bool
chkAInout (AInout { ainout_wire = wire }) = isInout_ (aType wire)

isBit :: AType -> Bool
isBit (ATBit _) = True
isBit _ = False

isBit1 :: AType -> Bool
isBit1 (ATBit sz) = (sz == 1)
isBit1 _ = False

isString :: AType -> Bool
isString (ATString _) = True
isString _ = False

isReal :: AType -> Bool
isReal (ATReal) = True
isReal _ = False

isClock :: AType -> Bool
isClock t = t == aTClock

isReset :: AType -> Bool
isReset t = t == aTReset

isInout_ :: AType -> Bool
isInout_ (ATAbstract i _) = i == idInout_
isInout_ _ = False

isForeignArg :: AType -> Bool
isForeignArg  e = isBit e || isString e || isReal e
--isBitOrString :: AType -> Bool
--isBitOrString e = isBit e || isString e
isBitOrInout_ :: AType -> Bool
isBitOrInout_ e = isBit e || isInout_ e

-- compare 2 types considering string sizes
compatTypesWthStr :: AType -> AType -> Bool
compatTypesWthStr (ATString ms1) (ATString ms2) = isNothing ms1 || isNothing ms2 || ms1 == ms2
compatTypesWthStr (ATArray sz1 t1) (ATArray sz2 t2) = (sz1 == sz2) && (compatTypesWthStr t1 t2)
compatTypesWthStr t1 t2                         = t1 == t2


isRelOp :: PrimOp -> Bool
isRelOp p = p `elem` [ PrimEQ, PrimULE, PrimULT, PrimSLE, PrimSLT, PrimEQ3 ]

isShift :: PrimOp -> Bool
isShift p = p `elem` [ PrimSL, PrimSRL, PrimSRA ]

tracePP :: Show a => String -> a -> Bool -> Bool
tracePP s x True = True
tracePP s x False = trace ("acheck:" ++ s ++ "\n" ++ show x) False
