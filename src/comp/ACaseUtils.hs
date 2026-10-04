-- | Pure case-expression lowering shared by the Verilog and Bluesim backends.
-- Kept with the IR utilities so using these rewrites does not import an
-- optimizer or a solver implementation.
module ACaseUtils
    ( aExpandDynSel, aInsertCaseDef, rmDupsInCasePairs, isInt ) where

import Warmup ()
import ASyntax
import ASyntaxUtil(AExprs(..))
import ErrorUtil(internalError)
import IntLit(IntLit(..), ilDec)
import PPrint(ppReadable)
import Prim(PrimOp(..))
import Util(allSame, flattenPairs, initOrErr, lastOrErr, makePairs, tracep)
import qualified Data.Set as S

-- These detailed traces were disabled in AOpt as well.
debug2 :: Bool
debug2 = False

expandVarRef :: (AId -> AExpr) -> AExpr -> AExpr
expandVarRef findf (ASDef { ae_objid = aid }) = expandVarRef findf (findf aid)
expandVarRef _ e = e


aExpandDynSel :: (AExprs a) => Bool -> (AId -> AExpr) -> a -> a
aExpandDynSel stringOK findFn = mapAExprs expDynSel
  where
        expDynSel (APrim sel_i sel_ty PrimArrayDynSelect [arr_e, idx_e]) =
           case arr_e of
             ASDef _ i ->
                 let arr_e' = findFn i
                 in  expDynSel
                         (APrim sel_i sel_ty PrimArrayDynSelect [arr_e', idx_e])
             APrim arr_i arr_ty PrimBuildArray elem_es ->
               let idx_ty = ae_type idx_e
                   max_idx = case idx_ty of
                               ATBit sz -> (2^sz) - 1
                               _ -> internalError ("aExpandDynSel: idx_ty")
                   -- number of arms is the min of the elems and the max index
                   arms = zip [0..max_idx] elem_es
                   -- make the last string be the default, if necessary
                   (arms_init, arms_last) =
                       (initOrErr "aExpandDynSel: init" arms,
                        lastOrErr "aExpandDynSel: last" arms)
                   mkLit n = ASInt defaultAId idx_ty (ilDec n)
                   mkCaseArm (n, e) = (mkLit n, e)
               in
                 if (isStringType sel_ty) && (not stringOK)
                 then
                   -- Verilog has to use if expressions for non-bit types
                   let foldFn (n, thn) els =
                         let cond = APrim sel_i aTBool PrimEQ [idx_e, mkLit n]
                         in  APrim sel_i sel_ty PrimIf [cond, thn, els]
                   in  foldr foldFn (snd arms_last) arms_init
                 else if (isStringType sel_ty)
                 then
                   -- We still want to avoid creating an ASAny of type String
                   -- so for now use the last string as the default
                   let case_arms = map mkCaseArm arms_init
                       default_e = snd arms_last
                   in  APrim sel_i sel_ty PrimCase
                          (idx_e : default_e : flattenPairs case_arms)
                 else
                   let case_arms = map mkCaseArm arms
                       default_e = ASAny (getArrayElemType arr_ty) Nothing
                   in  APrim sel_i sel_ty PrimCase
                          (idx_e : default_e : flattenPairs case_arms)
             _ -> internalError ("aExpandDynSel: unexpected array: " ++
                                 ppReadable arr_e)
        expDynSel e = e


-----

-- entry point for optimizing nested if-expressions in an expr,
-- converting them to case-expressions in some situations.
-- * nested ifs of 4 or more arms (including default) are converted
-- * XXX could check for completeness here?
-- * Note: this can inline references to other defs, to build the case
--
aInsertCaseDef :: Bool -> (AId -> AExpr) -> ADef -> ADef
aInsertCaseDef stringOK findFn (ADef i t e p) =
    ADef i t (aInsertCase stringOK findFn e) p

aInsertCase :: Bool -> (AId -> AExpr) -> AExpr -> AExpr
aInsertCase stringOK findFn (APrim i t p es) =
    let es' = map (aInsertCase stringOK findFn) es
    in  aPrimInsertCase stringOK findFn i t p es'
aInsertCase stringOK findFn (AMethCall t i m es) =
    let es' = map (aInsertCase stringOK findFn) es
    in  AMethCall t i m es'
aInsertCase stringOK findFn (AFunCall t i f isC es) =
    let es' = map (aInsertCase stringOK findFn) es
    in  AFunCall t i f isC es'
aInsertCase _ _ e = e

-- Convert any nested if-expressions that are checking the value of
-- one variable (e.g. "if (v == 1) else if (v == 2) ...") into a case
-- expression.  Allows arms such as "if (v == 3) || (v == 5)", but
-- they become separate arms in the case statement.
aPrimInsertCase :: Bool -> (AId -> AExpr) ->
                   AId -> AType -> PrimOp -> [AExpr] -> AExpr
aPrimInsertCase stringOK findFn aid t PrimIf es@[cond, _, _]
  | stringOK || not (isStringType t) =
    -- if the condition is of the form "(v == c) || (v2 == c2) || ...",
    -- then this will be Just [(v,c), (v2,c2), ...]
    let mcs = getConsts findFn (const True) cond
        res = case mcs of
                -- if all the v's are the same
                Just cs@((v,_):_) | allSame (map fst cs) ->
                    -- collect the ifs,
                    -- if there are any nested, convert to case
                    let (ces, d) = collIf findFn v [] (APrim aid t PrimIf es)
                        -- aPrim will check this again
                        -- but we do it here for the Bluesim backend
                        ces' = rmDupsInCasePairs ces
                    in  if length ces > 1
                        then APrim aid t PrimCase (v:d:flattenPairs ces')
                        else APrim aid t PrimIf es
                _ -> APrim aid t PrimIf es
    in  tracep debug2 ("aPrimInsertCase: " ++ ppReadable es) $
        tracep debug2 ("aPrimInsertCase: result: " ++ ppReadable res) $
        res
aPrimInsertCase stringOK findFn aid t p es = APrim aid t p es

-----


isInt :: AExpr -> Bool
isInt (ASInt _ _ _) = True
isInt _ = False


collIf :: (AId -> AExpr) -> AExpr -> [(AExpr, AExpr)] -> AExpr ->
          ([(AExpr, AExpr)], AExpr)
collIf findf v ces d =
    let -- this is either the original expr or an expanded variable ref
        d' = expandVarRef findf d
    in
        case (collIfPrim findf v ces d') of
            Just res -> res
            Nothing  -> (reverse ces, d)

-- This does the real work.
-- It returns (Just result) if optimization was possible
collIfPrim :: (AId -> AExpr) -> AExpr -> [(AExpr, AExpr)] -> AExpr -> Maybe ([(AExpr, AExpr)], AExpr)
collIfPrim findf v ces (APrim _ _ PrimIf [_, t, e]) | t == e =
        Just $ collIf findf v ces t
collIfPrim findf v ces (APrim _ _ PrimIf [cond, t, e])
  | (Just cs) <- getConsts findf (== v) cond =
        Just $ collIf findf v (zip (map snd cs) (repeat t) ++ ces) e
collIfPrim findf v ces (APrim _ _ PrimCase (v':d:ces')) | v == v' =
        Just (reverse ces ++ makePairs ces', d)
collIfPrim _ _ ces d = Nothing


-- Given a find function (from an Id to its Expr),
-- and a function which tells whether to consider the current expression
-- (either "const True" or "== v"),
-- return "Just vcs"
--    if the expression has one or more expressions like "(v == c)" OR'd
--    together, where vcs is a mapping from v to c
--    (if the expression is a def, follow its definition)
-- return Nothing otherwise
getConsts :: (AId -> AExpr) -> (AExpr -> Bool) -> AExpr -> Maybe [(AExpr, AExpr)]
getConsts find p (APrim _ _ PrimEQ [v, c]) | p v && isInt c = Just [(v, c)]
getConsts find p (APrim _ _ PrimBOr es) = mapM (getConsts find p) es >>= return . concat
getConsts find p (ASDef _ i) = getConsts find p (find i)
getConsts find _ _ = Nothing


rmDupsInCasePairs :: [(AExpr,AExpr)] ->  [(AExpr,AExpr)]
rmDupsInCasePairs prs = rmDups S.empty prs
    where
      rmDups :: S.Set Integer -> [(AExpr,AExpr)] -> [(AExpr,AExpr)]
      rmDups set [] = []
      rmDups set ( (p@(ASInt _ _ (IntLit { ilValue = n })), a) : rest )
          | n `S.member` set = rmDups set rest
          | otherwise = (p,a) : rmDups (S.insert n set) rest
      rmDups set ((p,a):rest) =
          internalError ("rmDupsInCasePairs: " ++ ppReadable p)

