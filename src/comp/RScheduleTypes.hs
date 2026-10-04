{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
-- | Resource allocation facts shared by a schedule codec and its consumers.
module RScheduleTypes (RAT, ratToNestedLists) where
import Warmup ()
import qualified Data.Map as M
import Data.List (sortBy)
import AUses (MethodId, UniqueUse)
import PPrint

type RAT = M.Map MethodId (M.Map UniqueUse Integer) -- resource allocation table

-- hack to avoid sorting order differences after switching from a list to a map
sortRatList :: [(MethodId, [(UniqueUse, Integer)])] -> [(MethodId, [(UniqueUse, Integer)])]
sortRatList = sortBy cmp
    where cmp x y = compare (ppString x) (ppString y)

ratToNestedLists :: RAT -> [(MethodId, [(UniqueUse, Integer)])]
ratToNestedLists = sortRatList . M.toList . M.map M.toList

instance PPrint RAT where
  pPrint d p = pPrint d p . ratToNestedLists

