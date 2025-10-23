module LiftCAFs(liftCAFs) where

import Control.Monad(zipWithM)
import Control.Monad.State.Strict
import qualified Data.Map as M
import Data.List(partition)
import Data.Maybe(isJust)
import qualified Data.Set as S

import CSyntax
import CSyntaxTypes
import CFreeVars
import Id
import Position(Position)
import IConvLet(reorderDs)
import qualified SCC(tsort, Graph)
import SymTab

import Debug.Trace(traceM)
import IOUtil(progArgs)
import Util(fromJustOrErr, mapSndM)
import ErrorUtil(internalError)
import PPrint(ppReadable)
import Flags(Flags, simplifyLiftCAFs)

trace_lift_cafs :: Bool
trace_lift_cafs = "-trace-lift-cafs" `elem` progArgs

-- Return an updated package and a boolean indicating whether any top-level
-- definitions were added.
liftCAFs :: Flags -> SymTab -> CPackage -> (CPackage, Bool)
liftCAFs flags symt pkg@(CPackage mi exps imps fixs ds includes)
  | simplifyLiftCAFs flags =
    let (ds', cafDefs) = runLState (initLState pkg symt) (lcaf initInfo ds)
    in (CPackage mi exps imps fixs (ds' ++ cafDefs) includes, not (null cafDefs))
  | otherwise = (pkg, False)

data LState = LState {
  -- source of unique numbers to append to CAF names
  cafNo :: Int,
  -- Map of CAF expressions to their saved name
  cafMap :: M.Map CExpr Id,
  -- Map of CAF names to their definitions
  cafDefMap :: M.Map Id CDefn,
  -- Name of the package being compiled (for qualifying CAF ids)
  packageName :: Id,
  symt :: SymTab,
  topNames :: S.Set Id
}

initLState :: CPackage -> SymTab -> LState
initLState (CPackage mi exps imps fixs ds includes) symt = LState {
  cafNo = 0,
  cafMap = M.empty,
  cafDefMap = M.empty,
  packageName = mi,
  symt = symt,
  -- We need this because the top-level names for converted instances
  -- (in the current package) are not in the symbol table.
  topNames = S.fromList $ [ i | (CValueSign (CDefT i _ _ _)) <- ds ]
  }

type L a = State LState a

runLState :: LState -> L a -> (a, [CDefn])
runLState s m = (a, M.elems $ cafDefMap s')
  where (a, s') = runState m s

chkTopLevelVar :: Id -> L Bool
chkTopLevelVar i = do
  ns <- gets topNames
  if i `S.member` ns then return True
  else do
    r <- gets symt
    case findVar r i of
      Just _ -> return True
      Nothing -> do
        cdm <- gets cafDefMap
        return $ isJust $ M.lookup i cdm

newCAFId :: Position -> L Id
newCAFId pos = do
  n <- gets cafNo
  mi <- gets packageName
  modify (\s -> s { cafNo = n + 1 })
  return $ qualId mi $ addIdProp (enumId "caf" pos n) IdPCAF

handleCAF :: CQType -> CExpr -> L Id
handleCAF cqt e = do
  m <- gets cafMap
  when (not $ null $ tv cqt) $
    internalError $ "LiftCAFs.handleCAF: Alleged CAF with free type variables:\n" ++ ppReadable(cqt, e) ++ "\n" ++ ppReadable m
  case e of
    CVar i -> do
      ok <- chkTopLevelVar i
      when (not ok) $ do
        cdm <- gets cafDefMap
        ns <- gets topNames
        internalError $
          "LiftCAFs.handleCAF: Alleged CAF variable not found in symbol table, cafDefMap or topNames: " ++
          ppReadable i ++ "\n" ++
          "cafDefMap: " ++ ppReadable cdm ++ "\n" ++
          "topNames: " ++ ppReadable ns 
      return i
    (CApply v@(CVar _) []) -> do
      when trace_lift_cafs $ traceM $ "handleCAF (CApply (CVar _) []): " ++ ppReadable e ++ "\n" ++ show e
      handleCAF cqt v
    otherwise ->
      case M.lookup e m of
        -- identical CAF already lifted
        Just i -> return i
        Nothing -> do
          cafId <- newCAFId (getPosition e)
          -- CAFs should have no type variables to generalize (which we checked above)
          let cafDef = CValueSign (CDefT cafId [] cqt [CClause [] [] e])
          when trace_lift_cafs $ traceM $ "adding CAF (LiftCAFs.handleCAF): " ++ ppReadable cafDef
          modify (\s -> s { cafMap = M.insert e cafId (cafMap s),
                            cafDefMap = M.insert cafId cafDef (cafDefMap s)
                          })
          return cafId
  
data LiftInfo = LiftInfo {
  -- Variables that are locally bound (not allowed in CAFs)
  boundIds  :: S.Set Id,
  -- Required expression substitutions
  exprSubst :: M.Map Id CExpr
  }

initInfo :: LiftInfo
initInfo = LiftInfo { boundIds = S.empty, exprSubst = M.empty }

dropVarsSubst :: S.Set Id -> M.Map Id CExpr -> M.Map Id CExpr
dropVarsSubst boundHere m = M.filterWithKey chkSubst m
  where chkSubst i e
          -- Checking the free variables of e may be overkill, but Simplify
          -- had a bunch of variable-capture bugs, so let's be careful
          | boundHere `S.disjoint` (snd $ getFVE e) = i `S.notMember` boundHere
          -- We can't simply drop the bad substitution because we have dropped the def that it came from
          | otherwise = internalError $ "LiftCAFs.dropVarsSubst (substitution capture): " ++ ppReadable (boundHere, i , e, m)

addBoundVars :: S.Set Id -> LiftInfo -> LiftInfo
addBoundVars boundHere info = LiftInfo { boundIds = boundIds',
                                         exprSubst = exprSubst'
                                       }
  where boundIds' = S.union boundHere (boundIds info)
        exprSubst' = dropVarsSubst boundHere (exprSubst info)

-- Used when checking isCAF for lets. In a let, the locally bound variables
-- do not stand in the way of being a CAF.
dropBoundVars :: S.Set Id -> LiftInfo -> LiftInfo
dropBoundVars dropHere info = LiftInfo { boundIds = boundIds',
                                         exprSubst = exprSubst'
                                       }
  where boundIds' = boundIds info `S.difference` dropHere
        exprSubst' = dropVarsSubst dropHere (exprSubst info)

addSubst :: Id -> CExpr -> LiftInfo -> LiftInfo
addSubst i e info@(LiftInfo { boundIds = boundIds, exprSubst = exprSubst })
  -- This disjointness check is probably overkill
  | boundIds `S.disjoint` (snd $ getFVE e) =
      -- If we are adding a subst for a previously bound id we are shadowing it
      -- and it is effectively not bound if we encounter it again in this context.
      info { boundIds = S.delete i boundIds,
             exprSubst = M.insert i e exprSubst }
  | otherwise = internalError $ "LiftCAFs.addSubst attempt to add captured substitution? " ++ ppReadable (i, e, boundIds)


handleNonCSEDefs :: LiftInfo -> [CDefl] -> L LiftInfo
handleNonCSEDefs info [] = return info
handleNonCSEDefs info ds = do
  cafIds <- mapM newCAFId $ map getPosition ds
  let newSubstPairs = [ (getLName d, CVar cafId) | (d, cafId) <- zip ds cafIds ]
      info' = foldr (uncurry addSubst) info newSubstPairs
  let mkNewDef (CLValueSign (CDefT i [] cqt cs) []) i' = do
        cs' <- lcaf info' cs
        return $ CValueSign (CDefT i' [] cqt cs')
      mkNewDef oldDef i' =
        internalError $ "handleNonCSEDefs.mkNewDef unexpected:\n" ++
                        "oldDef: " ++ ppReadable oldDef ++ "\n" ++
                        "i': " ++ ppReadable i' ++ "\n" ++
                        "cafIds: " ++ ppReadable cafIds ++ "\n" ++
                        "ds: " ++ ppReadable ds ++ "\n"
  ds' <- zipWithM mkNewDef ds cafIds
  when trace_lift_cafs $ traceM $ "adding CAFs (LiftCAFs.handleNonCSEDefs):\n" ++ ppReadable ds' 
  let newCafDefMap = M.fromList [ (i, d) | d@(CValueSign (CDefT i _ _ _)) <- ds' ]
  -- Nothing is added to cafMap so these defs are not csed against others
  modify (\s -> s { cafDefMap = M.union newCafDefMap (cafDefMap s) })
  return info'

class IsCAF a where
  isCAF :: LiftInfo -> a -> Bool

instance IsCAF CExpr where
  isCAF info (CVar i) = i `S.notMember` boundIds info
  -- If lets have not simplified away, it is not a CAF
  isCAF info (Cletrec ds e) = all (isCAF info') ds && isCAF info' e
    where info' = dropBoundVars (S.fromList $ map getLName ds) info
  isCAF info (Cletseq ds e) = chk info ds
    where chk :: LiftInfo -> [CDefl] -> Bool
          chk info [] = isCAF info e
          chk info (d:ds')
            | isCAF info d = chk info' ds'
            | otherwise = False
            where info' = dropBoundVars (S.singleton $ getLName d) info
  isCAF _    (CSelectT _ _) = True
  isCAF info (CApply f es) = all (isCAF info) (f:es)
  isCAF info (CTApply e ts) = null (tv ts) && isCAF info e
  isCAF info (CConT _ _ es) = all (isCAF info) es
  isCAF info (CStructT t fs) = null (tv t) && all (isCAF info) (map snd fs)
  isCAF _    (CAnyT _ _ t) = null (tv t)
  isCAF _    (CTaskApplyT _ _ _) = False
  isCAF _    (CLitT t l) = null (tv t)
  -- Technically a bit conservative, but very unlikely to be a meaningful CAF
  isCAF _    (Crules _ _) = False
  isCAF _    (CmoduleVerilogT _ _ _ _ _ _ _ _ _) = False
  isCAF _    (CForeignFuncCT _ _) = False
  -- Attributes are likely to be a CAF, but we don't want to move them around
  isCAF _    (Cattributes _) = False
  isCAF _    e = internalError("LiftCAFs.IsCAF(CExpr) unexpected: " ++ ppReadable e)

instance IsCAF CDefl where
  -- We have nowhere to put implicit conditions if we lift a def to the top level,
  -- so the qualifiers need to be null for a CAF.
  isCAF info (CLValueSign d me) = null me && isCAF info d
  isCAF _ defl@(CLValue _ _ _) = internalError $ "LiftCAFs.isCAF(CDefl) unexpected CLValue: " ++ ppReadable defl
  isCAF _ defl@(CLMatch _ _) = internalError $ "LiftCAFs.isCAF(CDefl) unexpected CLMatch: " ++ ppReadable defl

instance IsCAF CDef where
  isCAF info (CDefT i vs t cs) = null vs && null (tv t) && all (isCAF info) cs
  isCAF _ def = internalError $ "LiftCAFs.isCAF unexpected CDef: " ++ ppReadable def

instance IsCAF CClause where
  -- functions are not worth lifting to the top level
  isCAF info (CClause ps qs e) = null ps && null qs && isCAF info e
  -- = qsCAF && isCAF info' e
    -- where (qsCAF, info') = isCAFQuals info qs

isCAFQuals :: LiftInfo -> [CQual] -> (Bool, LiftInfo)
isCAFQuals info [] = (True, info)
isCAFQuals info (CQFilter e:qs) = (isCAF info e && restCAF, info)
  where (restCAF, info') = isCAFQuals info qs
isCAFQuals info (CQGen _ p e:qs) = (isCAF info' e && restCAF, info'')
    where boundHere = getPV p
          info' = dropBoundVars boundHere info
          (restCAF, info'') = isCAFQuals info' qs

class LiftCAFs a where
  lcaf :: LiftInfo -> a -> L a

instance (LiftCAFs a) => LiftCAFs [a] where
  lcaf info xs = mapM (lcaf info) xs

instance LiftCAFs CDefn where
  -- We are allowing self-references in top-level definitions the same way
  -- in CAFs the same way we allow references to other definitions in CAFs.
  lcaf info (CValueSign def@(CDefT i _ _ _)) = do
    def' <- lcaf info def
    let newFreeVars = S.toList $ snd (getFVD def') `S.difference` boundIds info
    chkFree <- mapM chkTopLevelVar newFreeVars
    when (not $ and chkFree) $
      internalError $ "LiftCAFs.CDefn free non top-level vars:\n" ++
                      "newFreeVars: " ++ ppReadable newFreeVars ++ "\n" ++
                      "chkFree: " ++ ppReadable chkFree ++ "\n" ++
                      "bad Ids: " ++ ppReadable [ i | (i, ok) <- zip newFreeVars chkFree, not ok ] ++
                      "boundIds: " ++ ppReadable (boundIds info) ++ "\n" ++
                      "before: " ++ ppReadable def ++
                      "after: " ++ ppReadable def'
    return $ CValueSign def'
  lcaf _    d = return d

instance LiftCAFs CClause where
  lcaf info (CClause ps qs e) = do
    let boundHere = S.unions $ map getPV ps
        info' = addBoundVars boundHere info
    -- We can't use the LiftCAFs instance for [a] because the qualifiers are
    -- not independent - earlier quals bind variables for later ones (and the expr)
    (qs', info'') <- liftCAFsQuals info' qs
    e' <- lcaf info'' e
    return $ CClause ps qs' e'

liftCAFsQuals :: LiftInfo -> [CQual] -> L ([CQual], LiftInfo)
liftCAFsQuals info qs = liftCAFsQuals' info [] qs

-- Args: info, reversed processed quals, unprocessed quals
liftCAFsQuals' :: LiftInfo -> [CQual] -> [CQual] -> L ([CQual], LiftInfo)
liftCAFsQuals' info rqs [] = return (reverse rqs, info)
liftCAFsQuals' info rqs (CQFilter e:qs) = do
  e' <- lcaf info e
  let q' = CQFilter e'
  liftCAFsQuals' info (q':rqs) qs
liftCAFsQuals' info rqs (CQGen t p e : qs) = do
  -- e is bound to p, so does not get any bound variables from it
  e' <- lcaf info e
  let boundHere = getPV p
      info' = addBoundVars boundHere info
      q' = CQGen t p e'
  liftCAFsQuals' info' (q':rqs) qs

instance LiftCAFs CDefl where
  lcaf info (CLValueSign d me) = do
    (me', info') <- liftCAFsQuals info me
    d' <- lcaf info' d
    return $ CLValueSign d' me'
  lcaf info defl@(CLValue _ _ _) = internalError $ "LiftCAFs.lcaf unexpected CLValue: " ++ ppReadable defl
  lcaf info defl@(CLMatch _ _) = internalError $ "LiftCAFs.lcaf unexpected CLMatch: " ++ ppReadable defl

instance LiftCAFs CDef where
  lcaf info d@(CDefT i vs t cs) = do
    cs' <- lcaf info cs
    return $ CDefT i vs t cs'
  lcaf _ def = internalError $ "LiftCAFs.lcaf unexpected CDef: " ++ ppReadable def

isSimple :: CExpr -> Bool
isSimple (CAnyT {}) = True
isSimple (CConT _ _ []) = True
isSimple (CLitT _ _) = True
isSimple (CTApply e _) = isSimple e
isSimple (CApply e []) = isSimple e
isSimple _ = False

liftCAFsDeflsSeq :: LiftInfo -> [CDefl] -> L ([CDefl], LiftInfo)
liftCAFsDeflsSeq info ds = liftCAFsDeflsSeq' info [] ds

-- Args: info, reversed processed defs, unprocessed defs
liftCAFsDeflsSeq' :: LiftInfo -> [CDefl] -> [CDefl] -> L ([CDefl], LiftInfo)
liftCAFsDeflsSeq' info rds [] = return (reverse rds, info)
liftCAFsDeflsSeq' info rds (d:ds) = do
  d'<- lcaf info d
  case d' of
    (CLValueSign (CDefT i [] t [CClause [] [] e]) [])
      -- Inline simple expressions
      | isSimple e && not (isKeepId i)-> do
          let info' = addSubst i e info
          -- drop the definition because we do not need it
          liftCAFsDeflsSeq' info' rds ds
      | isCAF info e && not (isKeepId i) -> do
          when trace_lift_cafs $ traceM $ "not inlined: " ++ ppReadable e ++ "\n" ++ show e
          i' <- handleCAF t e
          let info' = addSubst i (CVar i') info
          -- we can also drop the definition here because it moved to the top level
          liftCAFsDeflsSeq' info' rds ds
    otherwise -> do
      let info' = addBoundVars (S.singleton $ getLName d') info
      liftCAFsDeflsSeq' info' (d':rds) ds    

-- Note: Technically some recursive definitions could be CAFs, but we don't
-- try to lift them for simplicity. Recursive CAFs wouldn't CSE against each
-- other unless we handled alpha-renaming when checking for equality.
-- Also, recursive CAFs are not likely to be dictionaries (with the exception
-- of Eq (List a), which isn't much of a problem on its own).
liftCAFsDeflsRec :: LiftInfo -> [CDefl] -> L ([CDefl], [CDefl], LiftInfo)
liftCAFsDeflsRec info ds = do
  let localVars = S.fromList $ map getLName ds
      localDefMap = M.fromList [ (getLName d, d) | d <- ds ]
      getLocalDef i = fromJustOrErr msg $ M.lookup i localDefMap
        where msg = "liftCAFsDeflsRec.getLocalDef not found: " ++ ppReadable i ++ "\n" ++
                    "localDefMap: " ++ ppReadable localDefMap ++ "\n" ++
                    "ds: " ++ ppReadable ds
      info' = dropBoundVars localVars info
      isCAFDef :: S.Set Id -> CDefl -> Bool
      isCAFDef visited d
        -- If we've circled back, no need to keep looking for non-CAF definitions
        | i `S.member` visited = True
        | otherwise = isCAF info' d && all (isCAFDef visited') localRefs
        where i = getLName d
              visited' = S.insert i visited
              localRefs = [ getLocalDef i' | i' <- S.toList (snd $ getFVDl d), i' `S.member` localVars ] 
      (cafDefs, nonCafDefs) = partition (isCAFDef S.empty) ds

  when trace_lift_cafs $ traceM $ "cafDefs: " ++ ppReadable cafDefs
  when trace_lift_cafs $ traceM $ "nonCafDefs: " ++ ppReadable nonCafDefs

  -- no definitions to handle because they are all inlined or at the top level
  info'' <- handleCafRecDefs info' cafDefs

  let info''' = addBoundVars (S.fromList $ map getLName nonCafDefs) info''
  nonCafDefs' <- lcaf info''' nonCafDefs
  return ([], nonCafDefs', info''')

-- Compute the transitive closure of all the variables that depend
-- on a set of given variables. We use this to compute the transitive
-- closure of all the variables that depend on the variables in cycles
-- in handleCafDefs.
closeOver :: S.Set Id -> SCC.Graph Id -> (S.Set Id, SCC.Graph Id)
closeOver recVars [] = (recVars, [])
closeOver recVars graph = case partition needsRecVar graph of
                            ([], _) -> (recVars, graph)
                            (needs, graph') ->
                              let newRecVars = S.fromList $ map fst needs
                                  recVars' = S.union recVars newRecVars
                              in closeOver recVars' graph'
  where needsRecVar (i, is) = any (flip S.member $ recVars) (i:is)

handleCafRecDefs :: LiftInfo -> [CDefl] -> L LiftInfo
handleCafRecDefs info cafDefs = do
  let cafDefIds = [ i | (CLValueSign (CDefT i _ _ _) _) <- cafDefs ]
      cafDefIdSet = S.fromList cafDefIds

      -- We don't exclude i as we do in IConv because self-recursive definitions
      -- require the same special handling as other definition cycles.
      graph :: SCC.Graph Id
      graph = [ (i, cafDefRefs) |
                d@(CLValueSign (CDefT i _ _ _) _) <- cafDefs,
                let cafDefRefs = S.toList ((snd (getFVDl d)) `S.intersection` cafDefIdSet) ]

  -- Definitions may be unhandled because they have recursive references or because
  -- they are functions that don't turn into CSEd CAFs.
  case SCC.tsort graph of
    Right order -> do
      (unhandledDs, info') <- liftCAFsDeflsSeq info (reorderDs cafDefs order)
      handleNonCSEDefs info' unhandledDs
    Left cycles -> do
      let cycleVars = S.fromList $ concat cycles
          (recVars, nonRecGraph) = closeOver cycleVars graph   
          isRecD d = getLName d `S.member` recVars
          (recDs, nonRecDs) = partition isRecD cafDefs
          nonRecOrder =
            case SCC.tsort nonRecGraph of
              Right order
                | S.fromList (map fst nonRecGraph) == S.fromList (map getLName nonRecDs) -> order
                | otherwise ->
                  internalError $ "LiftCAFs.handleCafRecDefs nonRecDs and nonRecGraph inconsistent:\n" ++
                                  "nonRecDs: " ++ ppReadable nonRecDs ++ "\n" ++
                                  "nonRecGraph: " ++ ppReadable nonRecGraph ++ "\n" ++
                                  "full graph: " ++ ppReadable graph ++ "\n" ++
                                  "full graph cycles: " ++ ppReadable cycles ++ "\n" ++
                                  "all definitions: " ++ ppReadable cafDefs
              Left nonRecCycles ->
                internalError $ "LiftCAFs.handleCafRecDefs nonRecGraph has cycles: " ++ ppReadable nonRecCycles ++ "\n" ++
                                "nonRecGraph: " ++ ppReadable nonRecGraph ++ "\n" ++
                                "full graph: " ++ ppReadable graph ++ "\n" ++
                                "full graph cycles: " ++ ppReadable cycles ++ "\n" ++
                                "all definitions: " ++ ppReadable cafDefs
      (unhandledSeqDs, info') <- liftCAFsDeflsSeq info (reorderDs nonRecDs nonRecOrder)
      handleNonCSEDefs info' (unhandledSeqDs ++ recDs)

cLetSeq :: [CDefl] -> CExpr -> CExpr
cLetSeq [] e = e
cLetSeq ds e = Cletseq ds e

cLetRec :: [CDefl] -> CExpr -> CExpr
cLetRec [] e = e
cLetRec ds e = Cletrec ds e

instance LiftCAFs CExpr where
  lcaf info orig@(CVar i) = return $ M.findWithDefault orig i (exprSubst info)
  lcaf info (Cletseq ds e) = do
    (ds', info') <- liftCAFsDeflsSeq info ds
    e' <- lcaf info' e
    return $ cLetSeq ds' e'
  lcaf info (Cletrec ds e) = do
    (nonRecDs', recDs', info') <- liftCAFsDeflsRec info ds
    e' <- lcaf info' e
    return $ cLetSeq nonRecDs' $ cLetRec recDs' e'
  lcaf _    orig@(CSelectT _ _) = return orig
  lcaf info (CApply f es) = do
    f' <- lcaf info f
    es' <- lcaf info es
    return $ CApply f' es'
  lcaf info (CTApply e ts) = do
    e' <- lcaf info e
    return $ CTApply e' ts
  lcaf info (CConT t i es) = do
    es' <- lcaf info es
    return $ CConT t i es'
  lcaf info (CStructT t fs) = do
    fs' <- mapSndM (lcaf info) fs
    return $ CStructT t fs'
  lcaf _ orig@(CAnyT _ _ _) = return orig
  lcaf _ orig@(CLitT _ _) = return orig
  lcaf info (CTaskApplyT task t es) = do
    es' <- lcaf info es
    return $ CTaskApplyT task t es'
  lcaf info (Crules ps rs) = do
    rs' <- lcaf info rs
    return $ Crules ps rs'
  lcaf info (CmoduleVerilogT t m ui c rs ses fs sch ps) = do
    m' <- lcaf info m
    ses' <- mapSndM (lcaf info) ses
    return $ CmoduleVerilogT t m' ui c rs ses' fs sch ps
  lcaf _ orig@(CForeignFuncCT _ _) = return orig
  lcaf _ orig@(Cattributes _) = return orig
  lcaf _ e = internalError("LiftCAFs.lcaf unexpected: " ++ ppReadable e)

instance (LiftCAFs a) => LiftCAFs (Maybe a) where
  lcaf _ Nothing = return Nothing
  lcaf info (Just x) = fmap Just $ lcaf info x

instance LiftCAFs CRule where
  lcaf info (CRule rps mi qs e) = do
    mi' <- lcaf info mi
    (qs', info') <- liftCAFsQuals info qs
    e' <- lcaf info' e
    return $ CRule rps mi' qs' e'
  lcaf info (CRuleNest rps mi qs rs) = do
    mi' <- lcaf info mi
    (qs', info') <- liftCAFsQuals info qs
    rs' <- lcaf info' rs
    return $ CRuleNest rps mi' qs' rs'

