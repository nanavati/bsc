-- | Type normalization shared by elaboration and internal type checking.
-- The implementation is the original normalizer, independent of elaboration.
module ITypeNormalize (fullTypeNormalizer) where

import Warmup ()
import qualified Data.Map as M
import Changed
import CType(TISort(..))
import ErrorUtil(internalError)
import IConv(iConvT)
import ISyntax
import ISyntaxUtil
import IOUtil(progArgs)
import PPrint
import PhaseConfig(TypeSolverFlags)
import SymTab(SymTab)
import Util(tracep)

doTraceATFCache :: Bool
doTraceATFCache = elem "-trace-atf-cache" progArgs

doTraceATFCacheMiss :: Bool
doTraceATFCacheMiss = doTraceATFCache || elem "-trace-atf-cache-miss" progArgs

-- Type normalization function used in evaluation.
-- Fully traverse and reduce all type function applications where possible.
fullTypeNormalizer :: TypeSolverFlags -> SymTab -> IATFCache -> IType -> Changed IType
fullTypeNormalizer _ _ _ (ITCon _ _ _) = Unchanged
fullTypeNormalizer _ _ _ (ITNum _)     = Unchanged
fullTypeNormalizer _ _ _ (ITStr _)     = Unchanged
fullTypeNormalizer _ _ _ (ITVar _)     = Unchanged
fullTypeNormalizer flags symt cache (ITForAll i k t) = changed1 (ITForAll i k) t'
  where t' = fullTypeNormalizer flags symt cache t
fullTypeNormalizer flags symt cache t@(ITAp _ _)
    | (f@(ITCon atfId _ (TIatf { atf_param_idxs = pIdxs })), as) <- splitITAp t
    , length as == length pIdxs  -- Only attempt to reduce type functions that are fully applied.
    , as' <- map (changedOrId $ fullTypeNormalizer flags symt cache) as
    , all canNorm as'
    = Changed $ case M.lookup (atfId, as') cache of
        Just result ->
          tracep doTraceATFCache
            ("fullTypeNormalizer - ATF cache hit: " ++ ppReadable (atfId, as') ++
             " -> " ++ ppReadable result)
            result
        Nothing -> normTFun $ foldl ITAp f as'
  where -- The cache is keyed on concrete types; ITVar and ITForAll can't be looked up
        canNorm (ITVar _)        = False
        canNorm (ITForAll _ _ _) = False
        canNorm (ITAp f a)       = canNorm f && canNorm a
        canNorm _                = True
        normTFun t =
          let t' = tracep doTraceATFCacheMiss
                     ("fullTypeNormalizer - ATF cache miss: " ++ ppReadable t)
                     (iConvT flags symt $ iToCT t)
          in case splitITAp t' of
               ((ITCon _ _ (TIatf {})), _) -> internalError $
                    "fullTypeNormalizer - unsimplified: " ++ ppReadable (t,t')
               _ -> t'
fullTypeNormalizer flags symt cache (ITAp f a) = changed2 normITAp f a f' a'
  where f' = fullTypeNormalizer flags symt cache f
        a' = fullTypeNormalizer flags symt cache a

