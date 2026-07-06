module ContractCheck(checkDeclaredContract,
                     ContractStmt(..), readContract,
                     contractIdForIfc, signatureIdForIfc,
                     readSignatureKinds,
                     imposeDeclared, markMustHigh,
                     declaredConventions,
                     pinoutErrs, pinoutSummary) where

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
import Data.Char(isAlphaNum)
import Data.List(nub, intercalate, group, sort, (\\))

import Error(ErrorHandle, ErrMsg(..), bsError)
import Position(Position)
import Id
import Util(ordPair, uniquePairs)
import FStringCompat(mkFString, concatFString)
import CType(Type(..), leftCon, getArrows)
import CSyntax(CQType(..))
import ISyntax
import SchedInfo(SchedInfo(..), MethodConflictInfo(..))
import VModInfo(VModInfo, VSchedInfo, VMethodConflictInfo, VArgInfo(..),
                VeriPortProp(..),
                vSched, vFields, vArgs, VFieldInfo(..), VName(..),
                getVNameString, lookupInputClockWires, lookupInputResetWire)

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

-- ==================================================
-- Shared structural-reader machinery
--
-- Reduce an expression to a recognizable head applied to value
-- arguments, resolving the typechecker's local bindings on the way:
-- dictionary lets arrive as beta redexes (`IAps (ILam d _ body)
-- [dict]`), and variables bound by them are resolved through an
-- environment.  Referenced top-level definitions are never unfolded,
-- so any real computation stops the reader.  Bound variables are
-- unique after typecheck, so one flat environment suffices.

type REnv a = M.Map Id (IExpr a)

whead :: REnv a -> IExpr a -> (REnv a, IExpr a, [IExpr a])
whead env e0 = go env e0 []
  where
    go env' (IAps f _ es) as = go env' f (es ++ as)
    go env' (ILam v _ b) (a:as) = go (M.insert v a env') b as
    go env' (ILAM _ _ b) as = go env' b as
    go env' (IVar v) as | Just d <- M.lookup v env' = go env' d as
    go env' h as = (env', h, as)

-- a string-literal argument: literals arrive wrapped (fromString
-- dictionary application after typecheck), so collect string-literal
-- leaves without unfolding referenced definitions, and require
-- exactly one
readStr1 :: Either String String -> REnv a -> IExpr a -> Either String String
readStr1 err env e = case collectStrs env e of
                       [s] -> Right s
                       _ -> err
  where
    collectStrs _ (ICon _ (ICString { iStr = s })) = [s]
    collectStrs env' (IAps f _ es) = concatMap (collectStrs env') (f:es)
    collectStrs env' (ILam _ _ b) = collectStrs env' b
    collectStrs env' (ILAM _ _ b) = collectStrs env' b
    collectStrs env' (IVar v) | Just d <- M.lookup v env' = collectStrs env' d
    collectStrs _ _ = []

-- the carriers live in the Prelude; cons/nil also have List reexports
isLibId :: [String] -> Id -> Bool
isLibId names i = getIdBaseString i `elem` names &&
                  getIdQualString i `elem` ["Prelude", "List"]

-- read a literal list spine.  Two spellings occur: applications of
-- the cons/nil functions (`cons x rest`, user-written defs), and the
-- Cons/Nil constructors whose single argument is the payload struct
-- (`Cons (List_$Cons x rest)`, compiler-emitted defs)
readListSpine :: Either String [b] -> (REnv a -> IExpr a -> Either String b)
              -> REnv a -> IExpr a -> Either String [b]
readListSpine err readElem env e =
  case whead env e of
    (env', ICon i _, [x, rest])
      | isLibId ["cons", "Cons"] i ->
          do v <- readElem env' x
             vs <- readListSpine err readElem env' rest
             return (v:vs)
    (env', ICon i _, [payload])
      | isLibId ["Cons"] i ->
          case whead env' payload of
            (env'', ICon j _, [x, rest])
              | getIdBaseString j == "List_$Cons" ->
                  do v <- readElem env'' x
                     vs <- readListSpine err readElem env'' rest
                     return (v:vs)
            _ -> err
    (_, ICon i _, _)
      | isLibId ["nil", "Nil"] i -> return []
    _ -> err

-- read a literal pair (PrimPair struct or evaluated tuple)
readPairWith :: Either String b -> (REnv a -> IExpr a -> IExpr a -> Either String b)
             -> REnv a -> IExpr a -> Either String b
readPairWith err readBoth env e =
  case whead env e of
    (env', ICon p pinf, [a, b])
      | getIdBaseString p == "PrimPair" || isTupleInfo pinf ->
          readBoth env' a b
    _ -> err
  where
    isTupleInfo (ICTuple {}) = True
    isTupleInfo _ = False

-- ==================================================
-- The contract reader

readContract :: IExpr a -> Either String [ContractStmt]
readContract = readListSpine notLiteral readStmt M.empty
  where
    notLiteral :: Either String b
    notLiteral = Left ("a contract must be a literal list of contract " ++
                       "statements (cons/nil of contractCF, contractSB, " ++
                       "contractSBR, contractC, contractAlwaysReady, " ++
                       "contractAlwaysEnabled), with method names as " ++
                       "string literals (no concatenation or computation)")

    readStmt env e =
      case whead env e of
        (env', ICon i _, [m1, m2])
          | Just rel <- relOf i ->
              do a <- readStr1 notLiteral env' m1
                 b <- readStr1 notLiteral env' m2
                 return (CRel a rel b)
        (env', ICon i _, [m])
          | isLibId ["contractAlwaysReady", "ContractAlwaysReady"] i ->
              fmap CAlwaysReady (readStr1 notLiteral env' m)
          | isLibId ["contractAlwaysEnabled", "ContractAlwaysEnabled"] i ->
              fmap CAlwaysEnabled (readStr1 notLiteral env' m)
        _ -> notLiteral

    relOf i = foldr pick Nothing ["CF", "SB", "SBR", "C"]
      where pick r acc | isLibId ["contract" ++ r, "Contract" ++ r] i = Just r
                       | otherwise = acc

-- ==================================================
-- The signature-def reader (sealing consumes the structure's kinds)

-- The (package-qualified) id of an interface's compiler-emitted
-- signature def: named after the *flattened* interface ("<ifc>_"),
-- sanitized exactly as GenWrap's mkSignatureDef does
signatureIdForIfc :: Id -> Id
signatureIdForIfc ifcId =
    let sane c = if isAlphaNum c then c else '_'
        base = "signature_" ++ map sane (getIdBaseString ifcId ++ "_")
    in  setIdBase ifcId (mkFString base)

-- Read a compiler-emitted signature def -- a literal
-- List (String, List (String, String)) of (flattened path, slots) --
-- returning (path, kind) for every entry that carries a "kind" slot
readSignatureKinds :: IExpr a -> Either String [(String, String)]
readSignatureKinds e0 =
    fmap concat (readListSpine malformed readEntry M.empty e0)
  where
    malformed :: Either String b
    malformed = Left "malformed signature def"

    readEntry env e =
      readPairWith malformed
        (\ env' k v ->
           do path <- readStr1 malformed env' k
              slots <- readListSpine malformed readSlot env' v
              return (case lookup "kind" slots of
                        Just kv -> [(path, kv)]
                        Nothing -> []))
        env e

    readSlot env e =
      readPairWith malformed
        (\ env' k v ->
           do sk <- readStr1 malformed env' k
              sv <- readStr1 malformed env' v
              return (sk, sv))
        env e

-- ==================================================
-- The check

-- From the module's original type, find the interface tycon and the
-- (package-qualified) id of its contract def.  The type's result is
-- the module type applied to the interface (`Module ifc`, or `m ifc`
-- under an IsModule context), so the interface is the argument of the
-- outermost application.
contractDefId :: CQType -> Maybe Id
contractDefId cqt = fmap contractIdForIfc (cqtIfcCon cqt)

-- the interface tycon of a module's original type
cqtIfcCon :: CQType -> Maybe Id
cqtIfcCon (CQType _ t) =
  case snd (getArrows t) of
    TAp _ ifcT -> leftCon ifcT
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

-- Seal a member's recorded boundary at the declared contract: the
-- returned schedule carries exactly the declared freedoms, and NO
-- inferred member fact remains parent-visible unless it is
-- declaration-derived (design doc A100).  Declared pairs get their
-- declared relation; unlisted pairs of distinct methods become
-- conflicting (unpromised freedoms are not carried through, so the
-- parent schedules against the declaration rather than this member's
-- accidents).
--
-- Self-relations are outside the pairwise contract language, so they
-- get declaration-side defaults keyed by the interface's signature
-- kinds (never copied from the member): value methods are self-CF
-- (reads are effect-free; guarded below against the member's own
-- schedule), action and actionvalue methods are self-C (single-use,
-- until capacity clauses exist).
--
-- Readiness folding: RDY_* faces cannot appear in contracts --
-- readiness is the method's own offer facet, and reading the offer
-- wire is conflict-free with everything (a property of the canonical
-- rendering, not a contract freedom).  So every pair involving a
-- RDY_* face is imposed as CF, after checking that the member's own
-- schedule actually grants that (bsc-generated boundaries always do;
-- this guards the assumption rather than trusting it).
--
-- No other refinement check happens here: the member was already
-- checked against this same declaration at its own compile (the
-- design's A78/A83 inversion).
-- Returns the sealed schedule together with the resolved ids of the
-- contractAlwaysEnabled methods (the caller stamps their enable ports
-- with VPmusthigh so the existing proof machinery enforces the
-- consumer obligation at each parent's compile).
imposeDeclared :: [ContractStmt] -> [(String, String)] -> VModInfo
               -> Either String (VSchedInfo, [Id])
imposeDeclared stmts kinds vmi =
  let old = vSched vmi
      omci = methodConflictInfo old
      meths = [ n | Method { vf_name = n } <- vFields vmi ]
      isRdyI m = take 4 (getIdBaseString m) == "RDY_"
      real = [ m | m <- meths, not (isRdyI m) ]
      rdys = [ m | m <- meths, isRdyI m ]
      kindOf m = lookup (getIdBaseString m) kinds

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
  in
  do
    -- the member's external-conflict markers are accidents the
    -- contract cannot express, so sealing cannot hide them soundly
    case sEXT omci of
      [] -> Right ()
      (m:_) -> Left ("method `" ++ getIdBaseString m ++
                     "' carries an external-conflict marker; such a " ++
                     "boundary cannot join a group yet")
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
    -- declaration-derived self-relations (A100)
    self_kinds <-
        mapM (\ m -> case kindOf m of
                       Just k -> Right (m, k)
                       Nothing ->
                           Left ("method `" ++ getIdBaseString m ++
                                 "' has no entry in the interface's " ++
                                 "signature def; such a boundary cannot " ++
                                 "join a group yet"))
             real
    case [ (m, k) | (m, k) <- self_kinds,
                    k `notElem` ["value", "action", "actionvalue"] ] of
      [] -> Right ()
      ((m, k):_) -> Left ("method `" ++ getIdBaseString m ++
                          "' has unexpected signature kind `" ++ k ++
                          "'; such a boundary cannot join a group yet")
    let self_cf = [ m | (m, k) <- self_kinds, k == "value" ] ++ rdys
        self_c  = [ m | (m, k) <- self_kinds,
                        k == "action" || k == "actionvalue" ]
    -- a sealed contractAlwaysEnabled is a caller obligation on an
    -- effectful method, and an unconditionally used method must be
    -- unconditionally offered (bsc's own always_enabled implies
    -- always_ready)
    ae_ids <- mapM resolve (nub [ m | CAlwaysEnabled m <- stmts ])
    let ar_names = [ m | CAlwaysReady m <- stmts ]
    case [ m | CAlwaysEnabled m <- stmts, m `notElem` ar_names ] of
      [] -> Right ()
      (n:_) -> Left ("contractAlwaysEnabled " ++ n ++ " requires " ++
                     "contractAlwaysReady " ++ n ++ " in the same " ++
                     "contract (an unconditionally used method must be " ++
                     "unconditionally offered)")
    case [ i | i <- ae_ids,
               kindOf i `notElem` [Just "action", Just "actionvalue"] ] of
      [] -> Right ()
      (i:_) -> Left ("contractAlwaysEnabled is declared for `" ++
                     getIdBaseString i ++ "', which is not an action " ++
                     "method (reads have no enable)")
    -- guard the value-method default like the readiness fold: the
    -- member's own schedule must grant the imposed freedom
    case [ m | m <- self_cf, not (isRdyI m),
               not (permCovers (True, True, True) (mciPerms omci m m)) ] of
      (m:_) -> Left ("value method `" ++ getIdBaseString m ++
                     "' is not conflict-free with itself in the " ++
                     "member's own schedule; such a boundary cannot " ++
                     "join a group yet")
      [] -> Right ()
    let unlisted = [ p | p <- map ordPair (uniquePairs real),
                     p `notElem` keys ]
        new_mci = MethodConflictInfo {
            sCF  = [ (a, b) | (a, "CF", b) <- decls ] ++ rdy_pairs ++
                   [ (m, m) | m <- self_cf ],
            sSB  = [ (a, b) | (a, "SB", b) <- decls ],
            sME  = [],
            sP   = [],
            sSBR = [ (a, b) | (a, "SBR", b) <- decls ],
            sC   = [ (a, b) | (a, "C", b) <- decls ] ++ unlisted ++
                   [ (m, m) | m <- self_c ],
            sEXT = [] }
    return (old { methodConflictInfo = new_mci }, ae_ids)

-- ==================================================
-- Declared method conventions (convention_<Ifc>): a sparse literal
-- list choosing boundary realizations per method.  v0 carries one
-- statement, conventionReadyValid (retractable ready/valid).  The
-- unwritten default is the classic enable convention.

conventionIdForIfc :: Id -> Id
conventionIdForIfc ifcId =
    setIdBase ifcId (concatFString [mkFString "convention_", getIdBase ifcId])

-- read a convention def: the method names declared ReadyValid
readConventions :: IExpr a -> Either String [String]
readConventions = readListSpine notLit readStmt M.empty
  where
    notLit :: Either String b
    notLit = Left ("a convention def must be a literal list of " ++
                   "conventionReadyValid statements, with method names " ++
                   "as string literals")
    readStmt env e =
      case whead env e of
        (env', ICon i _, [m])
          | isLibId ["conventionReadyValid", "ConventionReadyValid"] i ->
              readStr1 notLit env' m
        _ -> notLit

-- look up and read the declared conventions for the module's
-- interface; absence means every method keeps the classic default
declaredConventions :: M.Map Id (IExpr a) -> CQType
                    -> Either String [String]
declaredConventions alldefs cqt =
  case cqtIfcCon cqt of
    Nothing -> Right []
    Just ifcId ->
      case M.lookup (conventionIdForIfc ifcId) alldefs of
        Nothing -> Right []
        Just body ->
          case readConventions body of
            Left msg -> Left ("convention def `" ++
                              getIdBaseString (conventionIdForIfc ifcId) ++
                              "': " ++ msg)
            Right ns -> Right (nub ns)

-- stamp the caller obligation on the enable ports of the given
-- methods (sealed contractAlwaysEnabled clauses): VPmusthigh keys the
-- existing always-enabled proof obligation without changing the
-- instantiation wiring (unlike VPinhigh, the port stays connected)
markMustHigh :: [Id] -> VModInfo -> VModInfo
markMustHigh ms vmi = vmi { vFields = map upd (vFields vmi) }
  where
    upd f@(Method { vf_name = n, vf_enable = Just (vn, props) })
        | n `elem` ms && VPmusthigh `notElem` props =
            f { vf_enable = Just (vn, VPmusthigh : props) }
    upd f = f

-- ==================================================
-- Pinout equality (A100): the group mechanism reuses one emitted
-- instantiation verbatim across implementations, so module arguments
-- and per-method port shapes must be identical -- compared by wire,
-- not by logical name (a declared boundary may name its clocks and
-- resets differently from a computed one) and not by port properties
-- (const/reg legitimately differ between implementations).  This is
-- a mechanism precondition, not contract checking: no schedule or
-- path refinement happens here.

argWireDesc :: VModInfo -> VArgInfo -> String
argWireDesc vmi (ClockArg i) = "clock " ++ show (lookupInputClockWires i vmi)
argWireDesc vmi (ResetArg i) = "reset " ++ show (lookupInputResetWire i vmi)
argWireDesc _ (Param vn) = "param " ++ getVNameString vn
argWireDesc _ (Port (vn, _) _ _) = "port " ++ getVNameString vn
argWireDesc _ (InoutArg vn _ _) = "inout " ++ getVNameString vn

-- multiplicities 0 and 1 both mean a single set of ports (0 is the
-- declared-boundary spelling of an unserialized method), so they are
-- wire-compatible; above 1 the port sets replicate and must agree
methodShapeOf :: VFieldInfo -> ([VName], Maybe VName, Maybe VName, Integer)
methodShapeOf m = (map fst (vf_inputs m), fmap fst (vf_output m),
                   fmap fst (vf_enable m), max 1 (toInteger (vf_mult m)))

showMethodShape :: ([VName], Maybe VName, Maybe VName, Integer) -> String
showMethodShape (ins, out, en, mult) =
    "(args " ++ intercalate "," (map getVNameString ins) ++
    maybe "" ((", result " ++) . getVNameString) out ++
    maybe "" ((", enable " ++) . getVNameString) en ++
    ", mult " ++ show mult ++ ")"

-- enable-port properties worth surfacing in the pinout record
-- (conventions and obligations; empty for plain classic enables)
enPropsDesc :: VFieldInfo -> String
enPropsDesc (Method { vf_enable = Just (_, ps) })
    | not (null ps) =
        " enable-props:" ++ intercalate "," (map (drop 2 . show) ps)
enPropsDesc _ = ""

isMethodField :: VFieldInfo -> Bool
isMethodField (Method {}) = True
isMethodField _ = False

pinoutErrs :: VModInfo -> VModInfo -> [String]
pinoutErrs root_vmi alt_vmi =
  let root_meths = [ f | f@(Method {}) <- vFields root_vmi ]
      alt_meths  = [ f | f@(Method {}) <- vFields alt_vmi ]
      root_names = map vf_name root_meths
      alt_names  = map vf_name alt_meths

      names_missing = [ getIdBaseString n | n <- root_names,
                        n `notElem` alt_names ]
      names_extra   = [ getIdBaseString n | n <- alt_names,
                        n `notElem` root_names ]
      name_errs =
          (if null names_missing then []
           else ["it lacks method(s) " ++ intercalate ", " names_missing]) ++
          (if null names_extra then []
           else ["it has extra method(s) " ++ intercalate ", " names_extra])

      arg_errs = if map (argWireDesc root_vmi) (vArgs root_vmi) ==
                    map (argWireDesc alt_vmi) (vArgs alt_vmi)
                 then []
                 else ["its module arguments differ from the group's"]

      port_errs =
          [ "the ports of method " ++ getIdBaseString (vf_name rm) ++
            " differ from the group's: group " ++
            showMethodShape (methodShapeOf rm) ++
            " vs alternate " ++ showMethodShape (methodShapeOf am)
          | rm <- root_meths, am <- alt_meths, vf_name rm == vf_name am,
            methodShapeOf rm /= methodShapeOf am ]

      root_other = [ getIdBaseString (vf_name f)
                   | f <- vFields root_vmi, not (isMethodField f) ]
      alt_other  = [ getIdBaseString (vf_name f)
                   | f <- vFields alt_vmi, not (isMethodField f) ]
      other_errs =
          (if null (root_other \\ alt_other) then []
           else [ "it lacks interface field(s) " ++
                  intercalate ", " (root_other \\ alt_other) ]) ++
          (if null (alt_other \\ root_other) then []
           else [ "it has extra interface field(s) " ++
                  intercalate ", " (alt_other \\ root_other) ])
  in
      name_errs ++ arg_errs ++ port_errs ++ other_errs

-- a normalized, human-readable pinout record for the selection
-- manifest (the seed of the future surface fingerprint)
pinoutSummary :: VModInfo -> [(String, String)]
pinoutSummary vmi =
    [ ("arguments",
       intercalate "; " (map (argWireDesc vmi) (vArgs vmi))) ] ++
    [ (getIdBaseString (vf_name m),
       showMethodShape (methodShapeOf m) ++ enPropsDesc m)
    | m <- vFields vmi, isMethodField m ] ++
    [ (getIdBaseString (vf_name f), "interface field")
    | f <- vFields vmi, not (isMethodField f) ]
