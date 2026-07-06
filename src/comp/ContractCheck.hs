module ContractCheck(checkDeclaredContract) where

-- Declared interface contracts, checked at each implementation's own
-- compile (design doc A78/A83: no inference across boundaries; the
-- check direction is always "actual refines declared").
--
-- A contract is declared beside its interface by naming convention,
-- as a single string literal in a small normalized language:
--
--   String contract_Counter = "value SB incr; always_ready value";
--
-- Statements, separated by ';':
--   <m1> CF|SB|SBR|C <m2>   -- scheduling relation (SB: m1 before m2)
--   always_ready <m>        -- the method's offer is constant
--   always_enabled <m>      -- consumer assumption (recorded; the
--                           -- obligation binds callers, not members)
-- Unlisted method pairs are conflicting; self-pairs are outside the
-- language; RDY_* names never appear (readiness is the method's own
-- offer aspect, not a sibling method).

import qualified Data.Map as M
import Data.Char(isSpace)
import Data.List(nub, intercalate)

import Error(ErrorHandle, ErrMsg(..), bsError)
import Position(Position)
import Id
import FStringCompat(mkFString, concatFString)
import CType(Type(..), leftCon, getArrows)
import CSyntax(CQType(..))
import ISyntax
import SchedInfo(MethodConflictInfo(..))
import VModInfo(VMethodConflictInfo)

-- ==================================================
-- The permission lattice: what a relation grants for an ordered pair
-- (a, b): (parallel in one rule, a-then-b in one cycle, b-then-a)

relNeeds :: String -> Maybe (Bool, Bool, Bool)
relNeeds "CF"  = Just (True, True, True)
relNeeds "SB"  = Just (True, True, False)
relNeeds "SBR" = Just (False, True, False)
relNeeds "C"   = Just (False, False, False)
relNeeds _     = Nothing

-- the permissions an inferred schedule grants for the ordered pair
mciPerms :: VMethodConflictInfo -> Id -> Id -> (Bool, Bool, Bool)
mciPerms mci a b
  | symIn sCF = (True, True, True)
  | (a, b) `elem` sSB mci = (True, True, False)
  | (b, a) `elem` sSB mci = (True, False, True)
  | symIn sP = (True, False, False)
  | (a, b) `elem` sSBR mci = (False, True, False)
  | (b, a) `elem` sSBR mci = (False, False, True)
  | otherwise = (False, False, False)
  where symIn f = (a, b) `elem` f mci || (b, a) `elem` f mci

permCovers :: (Bool, Bool, Bool) -> (Bool, Bool, Bool) -> Bool
permCovers (np, na, nb) (ap_, aa, ab) = np <= ap_ && na <= aa && nb <= ab

-- how the inferred schedule describes the pair, for error messages
mciClassify :: VMethodConflictInfo -> Id -> Id -> String
mciClassify mci a b
  | symIn sCF = "CF"
  | (a, b) `elem` sSB mci = "SB"
  | (b, a) `elem` sSB mci = "SB in the opposite order"
  | symIn sP = "P"
  | (a, b) `elem` sSBR mci = "SBR"
  | (b, a) `elem` sSBR mci = "SBR in the opposite order"
  | any (\ g -> a `elem` g && b `elem` g) (sME mci) = "ME"
  | otherwise = "C"
  where symIn f = (a, b) `elem` f mci || (b, a) `elem` f mci

-- ==================================================
-- The contract language

data ContractStmt = CRel String String String     -- m1 rel m2
                  | CAlwaysReady String
                  | CAlwaysEnabled String

parseContract :: String -> Either String [ContractStmt]
parseContract s = mapM stmt (filter (not . null) (map trim (splitOn ';' s)))
  where
    trim = dropWhile isSpace . reverse . dropWhile isSpace . reverse
    splitOn c str = case break (== c) str of
                      (a, []) -> [a]
                      (a, _:rest) -> a : splitOn c rest
    stmt t = case words t of
      [m1, rel, m2] | rel `elem` ["CF", "SB", "SBR", "C"] ->
          Right (CRel m1 rel m2)
      ["always_ready", m] -> Right (CAlwaysReady m)
      ["always_enabled", m] -> Right (CAlwaysEnabled m)
      _ -> Left ("cannot parse contract statement `" ++ t ++ "'; " ++
                 "expected `<m1> CF|SB|SBR|C <m2>', `always_ready <m>', " ++
                 "or `always_enabled <m>'")

-- ==================================================
-- The check

-- From the module's original type, find the interface tycon and the
-- (package-qualified) id of its contract def.  The type's result is
-- the module type applied to the interface (`Module ifc`, or `m ifc`
-- under an IsModule context), so the interface is the argument of the
-- outermost application.
contractDefId :: CQType -> Maybe Id
contractDefId (CQType _ t) =
  case snd (getArrows t) of
    TAp _ ifcT ->
      case leftCon ifcT of
        Just ifcId ->
            Just (setIdBase ifcId
                    (concatFString [mkFString "contract_", getIdBase ifcId]))
        Nothing -> Nothing
    _ -> Nothing

-- read a def body that must be a single string literal; the literal
-- arrives wrapped (fromString dictionary application after
-- typecheck), so walk the expression collecting string-literal
-- leaves without unfolding referenced definitions, and require
-- exactly one
readStringLiteral :: IExpr a -> Either String String
readStringLiteral e0 =
    case collect e0 of
      [s] -> Right s
      _ -> Left ("a contract must be a single string literal " ++
                 "(no concatenation or computation)")
  where
    collect (ICon _ (ICString { iStr = s })) = [s]
    collect (IAps f _ es) = concatMap collect (f:es)
    collect (ILam _ _ b) = collect b
    collect (ILAM _ _ b) = collect b
    collect _ = []

-- The entry point: look up contract_<Ifc> for the module's interface;
-- if declared, parse it and check the inferred schedule against it.
checkDeclaredContract :: ErrorHandle
                      -> M.Map Id (IExpr a)     -- all defs (qualified)
                      -> CQType                 -- the module's original type
                      -> Id                     -- module name (for messages)
                      -> Position               -- module position
                      -> VMethodConflictInfo    -- inferred schedule
                      -> [Id]                   -- inferred always-ready methods
                      -> [Id]                   -- boundary method ids
                      -> IO ()
checkDeclaredContract errh alldefs cqt modId modPos mci rdyTrue meths =
  case contractDefId cqt of
    Nothing -> return ()
    Just cid ->
      case M.lookup cid alldefs of
        Nothing -> return ()      -- contracts are opt-in
        Just body -> do
          let errs = case readStringLiteral body of
                Left m -> [m]
                Right s -> case parseContract s of
                  Left m -> [m]
                  Right stmts -> concatMap (checkStmt mci rdyTrue meths) stmts
          if null errs
            then return ()
            else bsError errh
                   [ (modPos,
                      EGeneric ("module `" ++ getIdBaseString modId ++
                                "' does not satisfy the declared contract `"
                                ++ getIdBaseString cid ++ "': " ++ e))
                   | e <- errs ]

checkStmt :: VMethodConflictInfo -> [Id] -> [Id] -> ContractStmt -> [String]
checkStmt mci rdyTrue meths stmt =
  case stmt of
    CRel m1 rel m2 ->
      case (resolve m1, resolve m2) of
        (Left e, _) -> [e]
        (_, Left e) -> [e]
        (Right a, Right b)
          | a == b -> ["self pair (" ++ m1 ++ ", " ++ m2 ++
                       ") is outside the contract language"]
          | otherwise ->
              case relNeeds rel of
                Nothing -> ["unknown relation `" ++ rel ++ "'"]
                Just needed
                  | permCovers needed (mciPerms mci a b) -> []
                  | otherwise ->
                      [m1 ++ " " ++ rel ++ " " ++ m2 ++
                       " is declared but the module schedules them as " ++
                       mciClassify mci a b]
    CAlwaysReady m ->
      case resolve m of
        Left e -> [e]
        -- the constant set holds RDY_<m> faces for methods whose ready
        -- wire is constant, and the method id itself when an
        -- always_ready pragma removed the wire
        Right i | i `elem` rdyTrue -> []
                | any (\r -> getIdBaseString r == ("RDY_" ++ m)) rdyTrue -> []
                | otherwise ->
                    ["always_ready " ++ m ++ " is declared but the " ++
                     "method's readiness is not constantly true"]
    CAlwaysEnabled _ -> []   -- a consumer assumption; recorded, not
                             -- an obligation on the member
  where
    resolve n
      | take 4 n == "RDY_" =
          Left ("`" ++ n ++ "': RDY_* names do not appear in contracts; " ++
                "readiness is the method's own offer (use always_ready)")
      | otherwise =
          case [ i | i <- meths, getIdBaseString i == n ] of
            (i:_) -> Right i
            [] -> Left ("unknown method `" ++ n ++
                        "'; the interface's methods are " ++
                        intercalate ", "
                          (nub (map getIdBaseString meths)))
