module ContractCheck(checkDeclaredContract,
                     ContractStmt(..), readContract,
                     contractIdForIfc, imposeDeclared) where

-- Declared interface contracts, checked at each implementation's own
-- compile (design doc A78/A83: no inference across boundaries; the
-- check direction is always "actual refines declared").
--
-- A contract is declared beside its interface by naming convention,
-- as a literal list of typed statement values (the carrier lives in
-- the Prelude):
--
--   List#(ContractStmt) contract_Counter =
--      cons(contractSB("value", "incr"),
--      cons(contractAlwaysReady("value"), nil));
--
-- Statements:
--   contractCF/contractSB/contractSBR/contractC m1 m2
--                             -- scheduling relation (SB: m1 before m2)
--   contractAlwaysReady m     -- the method's offer is constant
--   contractAlwaysEnabled m   -- consumer assumption (recorded; the
--                             -- obligation binds callers, not members)
-- Unlisted method pairs are conflicting; self-pairs are outside the
-- language; RDY_* names never appear (readiness is the method's own
-- offer aspect, not a sibling method).
--
-- DURABILITY (design doc A87): there is deliberately NO textual
-- grammar for contracts -- a string surface would be a durable
-- artifact committed to before we have experience with contracts.
-- The typed carrier is the only surface; it evolves through ordinary
-- typed deprecation.  This module's ContractStmt is the compiler-side
-- image of that carrier, and readContract is a purely structural
-- reader (literal lists only, no evaluation).

import qualified Data.Map as M
import Data.List(nub, intercalate, group, sort)

import Error(ErrorHandle, ErrMsg(..), bsError)
import Position(Position)
import Id
import Util(ordPair, uniquePairs)
import FStringCompat(mkFString, concatFString)
import CType(Type(..), leftCon, getArrows)
import CSyntax(CQType(..))
import ISyntax
import SchedInfo(SchedInfo(..), MethodConflictInfo(..))
import VModInfo(VModInfo, VSchedInfo, VMethodConflictInfo,
                vSched, vFields, VFieldInfo(..))

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
-- The contract statements (compiler-side image of the Prelude carrier)

data ContractStmt = CRel String String String     -- m1 rel m2
                  | CAlwaysReady String
                  | CAlwaysEnabled String

-- ==================================================
-- Reading a declared contract from a def body
--
-- The body must be a literal list of statement values:
-- cons/Cons/nil/Nil spines (Prelude or List) whose elements are
-- applications of the Prelude statement constructors (or their
-- lower-case builder functions) to string literals.  Purely
-- structural -- referenced definitions are never unfolded, so any
-- computation is rejected.

readContract :: IExpr a -> Either String [ContractStmt]
readContract = readSpine M.empty
  where
    notLiteral = Left ("a contract must be a literal list of contract " ++
                       "statements (cons/nil of contractCF, contractSB, " ++
                       "contractSBR, contractC, contractAlwaysReady, " ++
                       "contractAlwaysEnabled), with method names as " ++
                       "string literals (no concatenation or computation)")

    readSpine env e =
      case whead env e of
        (env', ICon i _, [x, rest])
          | isLib ["cons", "Cons"] i ->
              do s <- readStmt env' x
                 ss <- readSpine env' rest
                 return (s:ss)
        (_, ICon i _, [])
          | isLib ["nil", "Nil"] i -> return []
        _ -> notLiteral

    readStmt env e =
      case whead env e of
        (env', ICon i _, [m1, m2])
          | Just rel <- relOf i ->
              do a <- readStr env' m1
                 b <- readStr env' m2
                 return (CRel a rel b)
        (env', ICon i _, [m])
          | isLib ["contractAlwaysReady", "ContractAlwaysReady"] i ->
              fmap CAlwaysReady (readStr env' m)
          | isLib ["contractAlwaysEnabled", "ContractAlwaysEnabled"] i ->
              fmap CAlwaysEnabled (readStr env' m)
        _ -> notLiteral

    relOf i = foldr pick Nothing ["CF", "SB", "SBR", "C"]
      where pick r acc | isLib ["contract" ++ r, "Contract" ++ r] i = Just r
                       | otherwise = acc

    -- the statement carrier lives in the Prelude; cons/nil also have
    -- List reexports
    isLib names i = getIdBaseString i `elem` names &&
                    getIdQualString i `elem` ["Prelude", "List"]

    -- reduce to a recognizable head applied to value arguments,
    -- resolving the typechecker's local bindings on the way: dictionary
    -- lets arrive as beta redexes (`IAps (ILam d _ body) [dict]`), and
    -- variables bound by them are resolved through an environment.
    -- Referenced top-level definitions are never unfolded, so any
    -- real computation still stops the reader.  Bound variables are
    -- unique after typecheck, so one flat environment suffices.
    whead env e0 = go env e0 []
      where
        go env' (IAps f _ es) as = go env' f (es ++ as)
        go env' (ILam v _ b) (a:as) = go (M.insert v a env') b as
        go env' (ILAM _ _ b) as = go env' b as
        go env' (IVar v) as | Just d <- M.lookup v env' = go env' d as
        go env' h as = (env', h, as)

    -- a method-name argument: string literals arrive wrapped
    -- (fromString dictionary application after typecheck), so collect
    -- string-literal leaves without unfolding referenced definitions,
    -- and require exactly one
    readStr env e = case collect env e of
                      [s] -> Right s
                      _ -> notLiteral
    collect _ (ICon _ (ICString { iStr = s })) = [s]
    collect env (IAps f _ es) = concatMap (collect env) (f:es)
    collect env (ILam _ _ b) = collect env b
    collect env (ILAM _ _ b) = collect env b
    collect env (IVar v) | Just d <- M.lookup v env = collect env d
    collect _ _ = []

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
    TAp _ ifcT -> fmap contractIdForIfc (leftCon ifcT)
    _ -> Nothing

-- the (package-qualified) id of an interface's contract def
contractIdForIfc :: Id -> Id
contractIdForIfc ifcId =
    setIdBase ifcId (concatFString [mkFString "contract_", getIdBase ifcId])

-- The entry point: look up contract_<Ifc> for the module's interface;
-- if declared, read it and check the inferred schedule against it.
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
          let errs = case readContract body of
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
                    ["contractAlwaysReady " ++ m ++ " is declared but the " ++
                     "method's readiness is not constantly true"]
    CAlwaysEnabled _ -> []   -- a consumer assumption; recorded, not
                             -- an obligation on the member
  where
    resolve n
      | take 4 n == "RDY_" =
          Left ("`" ++ n ++ "': RDY_* names do not appear in contracts; " ++
                "readiness is the method's own offer " ++
                "(use contractAlwaysReady)")
      | otherwise =
          case [ i | i <- meths, getIdBaseString i == n ] of
            (i:_) -> Right i
            [] -> Left ("unknown method `" ++ n ++
                        "'; the interface's methods are " ++
                        intercalate ", "
                          (nub [ s | i <- meths,
                                     let s = getIdBaseString i,
                                     take 4 s /= "RDY_" ]))

-- ==================================================
-- The imposition (mkOneOf / primMkGroup)

-- Impose a declared contract on a member's recorded boundary: the
-- returned schedule carries exactly the declared freedoms.  Declared
-- pairs get their declared relation; unlisted pairs of distinct
-- methods become conflicting (unpromised freedoms are not carried
-- through, so the parent schedules against the declaration rather
-- than this member's accidents); self-pairs keep the member's own
-- classification (they are outside the contract language).
--
-- Readiness folding: RDY_* faces cannot appear in contracts --
-- readiness is the method's own offer aspect, and reading the offer
-- wire is conflict-free with everything (a property of the canonical
-- rendering, not a contract freedom).  So every pair involving a
-- RDY_* face is imposed as CF, after checking that the member's own
-- schedule actually grants that (bsc-generated boundaries always do;
-- this guards the assumption rather than trusting it).
--
-- No other refinement check happens here: the member was already
-- checked against this same declaration at its own compile (the
-- design's A78/A83 inversion).
imposeDeclared :: [ContractStmt] -> VModInfo -> Either String VSchedInfo
imposeDeclared stmts vmi =
  let old = vSched vmi
      omci = methodConflictInfo old
      meths = [ n | Method { vf_name = n } <- vFields vmi ]
      isRdyI m = take 4 (getIdBaseString m) == "RDY_"
      real = [ m | m <- meths, not (isRdyI m) ]
      rdys = [ m | m <- meths, isRdyI m ]

      resolve s = case [ m | m <- real, getIdBaseString m == s ] of
                    (m:_) -> Right m
                    [] -> Left ("unknown method `" ++ s ++
                                "'; the boundary's methods are " ++
                                intercalate ", " (map getIdBaseString real))

      resolveStmt (CRel a r b) = do
          ma <- resolve a
          mb <- resolve b
          if ma == mb
            then Left ("self pair (" ++ a ++ ", " ++ b ++
                       ") is outside the contract language")
            else Right [(ma, r, mb)]
      resolveStmt (CAlwaysReady m) = resolve m >> Right []
      resolveStmt (CAlwaysEnabled m) = resolve m >> Right []

      isSelf (a, b) = a == b
  in
  do
    decls <- fmap concat (mapM resolveStmt stmts)
    let keys = [ ordPair (a, b) | (a, _, b) <- decls ]
    case [ k | (k:_:_) <- group (sort keys) ] of
      ((a, b):_) -> Left ("methods " ++ getIdBaseString a ++ " and " ++
                          getIdBaseString b ++ " are related more than " ++
                          "once in the contract")
      [] -> Right ()
    let rdy_pairs = [ (r, m) | r <- rdys, m <- real ] ++ uniquePairs rdys
        not_cf = [ r | (r, m) <- rdy_pairs,
                   not (permCovers (True, True, True) (mciPerms omci r m)) ]
    case not_cf of
      (r:_) -> Left ("the readiness of `" ++ drop 4 (getIdBaseString r) ++
                     "' is not conflict-free in the member's own " ++
                     "schedule; such a boundary cannot join a group yet")
      [] -> Right ()
    let unlisted = [ p | p <- map ordPair (uniquePairs real),
                     p `notElem` keys ]
        new_mci = MethodConflictInfo {
            sCF  = [ (a, b) | (a, "CF", b) <- decls ] ++ rdy_pairs ++
                   filter isSelf (sCF omci),
            sSB  = [ (a, b) | (a, "SB", b) <- decls ] ++
                   filter isSelf (sSB omci),
            sME  = [],
            sP   = filter isSelf (sP omci),
            sSBR = [ (a, b) | (a, "SBR", b) <- decls ] ++
                   filter isSelf (sSBR omci),
            sC   = [ (a, b) | (a, "C", b) <- decls ] ++ unlisted ++
                   filter isSelf (sC omci),
            sEXT = sEXT omci }
    return (old { methodConflictInfo = new_mci })
