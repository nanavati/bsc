module LiftCAFs(liftCAFs) where

import Control.Monad.State(State, runState)
import qualified Data.Map as M
import Id(Id)
import CSyntax
import SymTab

import Flags(Flags, simplifyLiftCAFs)

-- Return an updated package and a boolean indicating whether any top-level
-- definitions were added.
liftCAFs :: Flags -> SymTab -> CPackage -> (CPackage, Bool)
liftCAFs flags symt pkg@(CPackage mi exps imps fixs ds includes)
  | simplifyLiftCAFs flags =
    let (ds', cafDefs) = runLState (initLState symt) (lcaf ds)
    in (CPackage mi exps imps fixs (ds' ++ cafDefs) includes, not (null cafDefs))
  | otherwise = (pkg, False)

data LState = LState {

  -- source of unique numbers to append to CAF names
  cafNo :: Integer,

  -- Map of CAF expressions to their saved name and top-level definition
  cafMap :: M.Map CExpr (Id, CDefn),

  symt :: SymTab

}

initLState :: SymTab -> LState
initLState symt = LState { cafNo = 0, cafMap = M.empty, symt = symt }

runLState :: LState -> L a -> (a, [CDefn])
runLState s m = (a, map snd $ M.elems $ cafMap s')
  where (a, s') = runState m s

type L a = State LState a

class LiftCAFs a where
  lcaf :: a -> L a

instance (LiftCAFs a) => LiftCAFs [a] where
  lcaf xs = mapM lcaf xs

instance LiftCAFs CDefn where
  lcaf d = return d
