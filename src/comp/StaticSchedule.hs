-- | Representation of the existing static scheduler, separate from common IR.
module StaticSchedule
    ( ASchedule(..), AScheduler(..)
    , getSchedulerIds, dropScheduleIds, dropSchedulerIds ) where

import Prelude hiding ((<>))
import Warmup ()
import ASyntax(ARuleId)
import Data.List(intersect, (\\))
import ErrorUtil(internalError)
import Eval
import PPrint

-- parallel rule groups; total order on state
-- (first rule in the list writes, present only if there are state conflicts)
data ASchedule = ASchedule {
        asch_scheduler :: [AScheduler],
                        -- list of ruleids is REVERSE ordering for execution
        asch_rev_exec_order :: [ARuleId]
    }
        deriving (Eq, Show)

instance NFData ASchedule where
    rnf (ASchedule sched order) = rnf2 sched order

newtype AScheduler =
          -- esposito: (r,f) s.t.
          --   f is the list of conditions for which
          --        rule r should not fire when enabled
          --   f is expressed as a
          --        list of rules that conflict with the rule r.
          --   In the future, f should be a list of list of rules,
          --      where the sublists are a list of rules which when
          --      enabled should disable the firing of r.
          --      So [[a,b],[c],[d,e,f]] = !(ab) && !c && !(def)
    ASchedEsposito [(ARuleId, [ARuleId])]
        deriving (Eq, Show)

instance NFData AScheduler where
    rnf (ASchedEsposito fs) = rnf fs

getSchedulerIds :: AScheduler -> [ARuleId]
getSchedulerIds (ASchedEsposito fs) = map fst fs

dropScheduleIds :: [ARuleId] -> ASchedule -> ASchedule
dropScheduleIds dropIds (ASchedule gs order) = (ASchedule gs' order')
  where order' = order \\ dropIds
        gs' = map (dropSchedulerIds dropIds) gs

dropSchedulerIds :: [ARuleId] -> AScheduler -> AScheduler
dropSchedulerIds dropIds sch =
  let result = dropSchedulerIds' dropIds sch in
      -- paranoia check
      if (not . null) (dropIds `intersect` getSchedulerIds result) then
         internalError("ASyntax.dropSchedulerIds " ++ ppReadable dropIds ++
                       "\n" ++ ppReadable sch)
      else result

dropSchedulerIds' :: [ARuleId] -> AScheduler -> AScheduler
dropSchedulerIds' dropIds (ASchedEsposito fs) = ASchedEsposito fs'
  where fs' = [(rid, rs') | (rid, rs) <- fs,
                            not (rid `elem` dropIds),
                            let rs' = rs \\ dropIds]

instance PPrint ASchedule where
     pPrint d p (ASchedule groups order) = (text "parallel:" <+> pPrint d 0 groups)
                                           $+$ (text "order:" <+> pPrint d 0 (reverse order))

instance PPrint AScheduler where
     pPrint d p (ASchedEsposito fs) =
         let ppDep (r,cfs) = pPrint d 0 r <+> text "->" <+> pPrint d 0 cfs
         in  text "esposito:" <+> text "[" <> sep (punctuate (text ",") (map ppDep fs)) <> text "]"


