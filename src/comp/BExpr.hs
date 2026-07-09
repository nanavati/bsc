{-# LANGUAGE CPP #-}
module BExpr(BExpr, bNothing, bAdd, bImplies, bImpliesB) where

#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 804)
import Prelude hiding ((<>))
#endif

import qualified Data.Set as S
import PPrint
import ISyntax
import ISyntaxUtil
import Prim

--import Debug.Trace


-- A BExpr records information when is know to be true.
-- bNothing is no information
-- bAdd adds an additional fact
-- bImplies checks if the know facts implies an expression.
--  bImplies is allowed to answer False even if the implication
--  is true, but not the other way around.

bNothing :: BExpr a
bAdd :: IExpr a -> BExpr a -> BExpr a
bImplies :: BExpr a -> IExpr a -> Bool
bImpliesB :: BExpr a -> BExpr a -> Bool

-- The facts are a set of conjuncts known to be true.  Queries and new
-- facts are split into their conjuncts (getAnds . norm); a query is
-- implied when every conjunct is a known fact.
newtype BExpr a = A (S.Set (IExpr a))

instance PPrint (BExpr a) where
    pPrint d p (A es) = text "(B" <+> pPrint d 0 (S.toList es) <> text ")"

bNothing = A (S.singleton iTrue)

bAdd e (A es) = A $ foldr S.insert es (get e)

-- The conjunct list is produced lazily (invert builds thunks and
-- getAnds streams the spine), so this stops at the first conjunct that
-- is not a known fact without ever materializing the rest of the
-- (possibly large) inverted expression.
bImplies (A es) e = all (`S.member` es) (get e)

bImpliesB b (A es) = all (bImplies b) (S.toList es)

get :: IExpr a -> [IExpr a]
get = getAnds . norm

-- split a PrimBAnd spine into its conjuncts (accumulator, no dedup:
-- the consumers are set operations, which deduplicate themselves)
getAnds :: IExpr a -> [IExpr a]
getAnds e0 = go e0 []
  where go (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) acc = go e1 (go e2 acc)
        go e acc = e : acc

norm :: IExpr a -> IExpr a
norm (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]) = invert e
norm e = e

invert :: IExpr a -> IExpr a
invert (IAps (ICon _ (ICPrim _ PrimBAnd)) _ [e1, e2]) = ieOr  (invert e1) (invert e2)
invert (IAps (ICon _ (ICPrim _ PrimBOr )) _ [e1, e2]) = ieAnd (invert e1) (invert e2)
invert (IAps (ICon _ (ICPrim _ PrimBNot)) _ [e]     ) = e
invert e = ieNot e
