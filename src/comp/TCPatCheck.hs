{-# LANGUAGE CPP #-}

-- | Pattern-match exhaustiveness and redundancy checking.
--
-- This implements the classic pattern-matrix "usefulness" analysis
-- (Luc Maranget, \"Warnings for pattern matching\", JFP 17(3), 2007),
-- the same foundation used by GHC's -Wincomplete-patterns and
-- -Woverlapping-patterns.
--
-- Because the typechecker rewrites literal patterns into boolean guards
-- (see 'rmPatLit' in TCMisc) before pattern typing, the checking cannot
-- run on the typed syntax: the original (pre-typechecking) clauses are
-- captured as 'PatMatchObligation's while the typechecker runs, the
-- pattern-column types are refined as the substitution grows, and the
-- obligations are checked once the enclosing top-level definition has
-- finished typechecking (see 'flushPatObligations' in TIMonad).
--
-- Guards are treated conservatively, as in GHC: an arm with guards
-- contributes nothing to coverage, and only guard-free arms can make a
-- later arm redundant.  Constructor patterns are resolved against the
-- (resolved) column type using the symbol table, so tagged unions,
-- enums, structs and tuples are all handled; literal matches over
-- @Bit n@, @UInt n@ and @Int n@ additionally know the finite domain of
-- the type, so covering all @2^n@ values is recognized as exhaustive
-- (which GHC's checker does not attempt for numeric literals).
module TCPatCheck(
    PatMatchContext(..),
    PatMatchRow(..),
    PatMatchObligation(..),
    mkClausesObligation,
    isGeneratedScrutinee,
    checkPatMatches
) where

import Data.List(find, nub, genericLength)
import Data.Maybe(isNothing)
import qualified Data.Map as M
import qualified Data.Set as S

import Classic(isClassic)
import Id
import PreIds(idBit, idUInt, idInt, idInteger, idReal, idChar,
              idPrimUnit, idPrimPair, idComma, tupleIds)
import Position
import Error(WMsg, ErrMsg(..))
import Flags(Flags, warnIncompletePatterns, warnOverlappingPatterns)
import CSyntax
import CFreeVars(getPV, getFVE, fvSetToFreeVars)
import CType
import Type(tString)
import Pred(expandSyn, Qual(..))
import qualified Pred(inst)
import Scheme
import Assump
import Subst(Types(..))
import SymTab
import ConTagInfo(ConTagInfo(..))
import IntLit
import Literal
import PFPrint

-- ---------------------------------------------------------------------------
-- Obligations: pattern matches recorded during typechecking

-- | What kind of source construct the match came from (for warning text)
data PatMatchContext
    = PMCase            -- ^ a case expression (or BSV case..matches)
    | PMDef Id          -- ^ the clauses of a definition
    deriving (Eq, Show)

data PatMatchRow = PatMatchRow {
    pmr_pos :: Position,     -- ^ position of the arm/clause
    pmr_pats :: [CPat],      -- ^ original (pre-typechecking) patterns
    pmr_guarded :: Bool,     -- ^ the arm has qualifiers (guards)
    pmr_gen_dflt :: Bool     -- ^ parser/deriving-inserted default arm
} deriving (Eq, Show)

data PatMatchObligation = PatMatchObligation {
    pmo_pos :: Position,          -- ^ position of the case/def
    pmo_ctx :: PatMatchContext,
    pmo_type :: Type,             -- ^ the clauses' function type; the first
                                  --   'pmo_ncols' arrow arguments are the
                                  --   pattern-column types
    pmo_ncols :: Int,
    pmo_rows :: [PatMatchRow]
} deriving (Eq, Show)

-- Only the function type needs the substitution; the patterns are
-- pre-typechecking syntax and contain no type variables.
instance Types PatMatchObligation where
    apSub s o = o { pmo_type = apSub s (pmo_type o) }
    tv o = tv (pmo_type o)

-- | Construct an obligation from the original clauses of a match, or
-- Nothing if the match should not be checked (compiler-generated code,
-- trivially exhaustive single wildcard clauses, malformed arities).
mkClausesObligation :: PatMatchContext -> Position -> Type -> [CClause]
                    -> Maybe PatMatchObligation
mkClausesObligation _ _ _ [] = Nothing
mkClausesObligation ctx pos ty cls@(CClause ps0 _ _ : _)
    -- definitions with compiler-generated names hold compiler-copied
    -- clauses (e.g. a typeclass default replicated into an instance,
    -- which was already checked at the class declaration)
    | PMDef i <- ctx, isBadId i || isRenamingId i = Nothing
    -- a definition with no patterns has nothing to report examples of
    -- (a guard-only definition can still fail to match, but there is
    -- no pattern to point at)
    | ncols == 0 = Nothing
    | any badArity cls = Nothing
    | any (clauseBindsGeneratedVar) cls = Nothing
    | trivial = Nothing
    | otherwise = Just (PatMatchObligation pos' ctx ty ncols (map row cls))
  where
    -- point definition warnings at the first clause, not the signature
    pos' = case (ctx, cls) of
             (PMDef _, c : _) -> rowPos c
             _ -> pos
    ncols = length ps0
    badArity (CClause ps _ _) = length ps /= ncols
    -- matches in compiler-generated code (deriving, parser desugaring)
    -- bind compiler-generated pattern variables
    clauseBindsGeneratedVar (CClause ps qs _) =
        any isGenVar (S.toList (S.unions (map getPV ps))) ||
        any qualBindsGeneratedVar qs
    qualBindsGeneratedVar (CQGen _ p _) = any isGenVar (S.toList (getPV p))
    qualBindsGeneratedVar (CQFilter _) = False
    isGenVar i = isBadId i || isRenamingId i
    -- a single unguarded clause of variable/wildcard patterns is
    -- trivially exhaustive and trivially irredundant (the common case
    -- for every ordinary definition, so worth filtering early)
    trivial = case cls of
                [CClause ps [] _] -> all isWildPat ps
                _ -> False
    isWildPat (CPVar _) = True
    isWildPat (CPAny _) = True
    isWildPat (CPAs _ p) = isWildPat p
    isWildPat _ = False
    row c@(CClause ps qs _) =
        PatMatchRow { pmr_pos = rowPos c,
                      pmr_pats = ps,
                      pmr_guarded = not (null qs),
                      pmr_gen_dflt = isGenDflt ps }
    rowPos (CClause (p:_) _ _) | getPosition p /= noPosition = getPosition p
    rowPos c = pos
    -- the BSV parser inserts an implicit "default: noop" arm (a CPAny
    -- carrying the case statement's own position) in statement contexts;
    -- deriving uses CPAny at noPosition
    isGenDflt [CPAny p] = p == pos || p == noPosition
    isGenDflt _ = False

-- | Is the scrutinee of a case expression compiler-generated?  The BSV
-- parser encodes plain @case@ (and @if@ with @matches@ conditions) as a
-- degenerate case on the unit struct with guard-only arms, and deriving
-- scrutinizes compiler-generated temporaries.
isGeneratedScrutinee :: CExpr -> Bool
isGeneratedScrutinee (CStruct _ i []) | qualEq i idPrimUnit = True
isGeneratedScrutinee e =
    any (\ i -> isBadId i || isRenamingId i) (fvSetToFreeVars (getFVE e))

-- ---------------------------------------------------------------------------
-- Normalized patterns

-- | A constructor (or the single implicit constructor of a struct),
-- resolved against the column type, with instantiated argument types.
data NConDesc = NConDesc {
    nc_typeId :: Id,        -- ^ qualified type id
    nc_name :: Id,          -- ^ constructor name (for witness rendering)
    nc_conNo :: Integer,    -- ^ identity within the type
    nc_isStruct :: Bool,    -- ^ the implicit constructor of a struct
    nc_isEnum :: Bool,      -- ^ member of an enum (no constructor has data)
    nc_argTypes :: [CType], -- ^ instantiated sub-column types
    nc_fieldIds :: [Id]     -- ^ field names (structs); [] for constructors
}

-- | Literal domains: Bit n and UInt n have the values [0, 2^n), Int n
-- has [-2^(n-1), 2^n-1); everything else is treated as unbounded.
data LitDomain = LDFinite Integer Integer NegRule  -- lo, hi (inclusive)
               | LDInfinite
    deriving (Eq)

-- | What a negated literal means at the type, mirroring the ranges
-- accepted by the conversion primitives at elaboration (see
-- PrimIntegerToBit\/UIntBits\/IntBits in IExpand)
data NegRule = NegWrap Integer  -- ^ Bit n: wraps; magnitude at most 2^(n-1)
             | NegNone          -- ^ UInt n: negative literals are invalid
             | NegExact         -- ^ Int n: the negated value must be in range
    deriving (Eq)

data LitKey = LKInt Integer | LKStr String | LKChar Char | LKReal Double
    deriving (Eq, Ord)

data NPat = NWild
          | NCon NConDesc [NPat]
          | NLit LitKey

-- | What a pattern column looks like, derived from its type
data ColKind = CKData Id [NConDesc]
             | CKStruct NConDesc
             | CKLit LitDomain
             | CKOpaque

-- ---------------------------------------------------------------------------
-- Column type analysis

colKind :: SymTab -> CType -> ColKind
colKind r t =
    let t' = expandSyn t
    in  case leftCon t' of
          Nothing -> CKOpaque
          Just tcid
            | tcid `qualEq` idBit || tcid `qualEq` idUInt ->
                case tyConArgs t' of
                  -- bound the width, so that the 2^n domain value stays
                  -- cheap to compute and compare
                  [n] | isTNum n, getTNum n <= 65536 ->
                    let w = getTNum n
                        neg = if tcid `qualEq` idBit && w > 0
                              then NegWrap (2^(w-1))
                              else NegNone
                    in  CKLit (LDFinite 0 (2^w - 1) neg)
                  _ -> CKLit LDInfinite
            | tcid `qualEq` idInt ->
                case tyConArgs t' of
                  [n] | isTNum n, getTNum n >= 1, getTNum n <= 65536 ->
                    let w = getTNum n
                    in  CKLit (LDFinite (negate (2^(w-1))) (2^(w-1) - 1)
                                        NegExact)
                  _ -> CKLit LDInfinite
            | any (qualEq tcid)
                  [idInteger, idReal, idChar, idStringTC] ->
                CKLit LDInfinite
            | otherwise ->
                case findType r tcid of
                  Just (TypeInfo (Just qtid) _ _ (TIdata cons is_enum) _) ->
                      case mapM (conDesc r qtid t' is_enum) cons of
                        Just ds | not (null ds) -> CKData qtid ds
                        _ -> CKOpaque
                  Just (TypeInfo (Just qtid) _ _ (TIstruct ss fs) _)
                    | isCheckableStruct ss ->
                      case structDesc r qtid t' fs of
                        Just d -> CKStruct d
                        Nothing -> CKOpaque
                  _ -> CKOpaque
  where
    isCheckableStruct SStruct = True
    isCheckableStruct (SDataCon _ _) = True
    -- tuples are the PrimPair interface in the Prelude
    isCheckableStruct (SInterface _) = True
    isCheckableStruct _ = False
    -- the type id of String (tString's TyCon)
    idStringTC = case tString of
                   TCon (TyCon i _ _) -> i
                   _ -> idInteger  -- unreachable

-- | Resolve one constructor of a data type at the given (expanded)
-- column type, computing its instantiated payload type.
conDesc :: SymTab -> Id -> CType -> Bool -> Id -> Maybe NConDesc
conDesc r qtid colty is_enum conName = do
    cis <- findCon r conName
    ci <- find (\ ci -> qualEq (ci_id ci) qtid) cis
    let (_ :>: Forall ks (_ :=> cty)) = ci_assump ci
        cti = ci_taginfo ci
    (argty, resty) <- splitArrow1 cty
    tsub <- tgenMatch resty colty
    vec <- mapM (\ n -> M.lookup n tsub) [0 .. length ks - 1]
    return (NConDesc { nc_typeId = qtid,
                       nc_name = conName,
                       nc_conNo = conNo cti,
                       nc_isStruct = False,
                       nc_isEnum = is_enum,
                       nc_argTypes = [expandSyn (Pred.inst vec argty)],
                       nc_fieldIds = [] })

-- | The single implicit constructor of a struct type, with instantiated
-- field types.
structDesc :: SymTab -> Id -> CType -> [Id] -> Maybe NConDesc
structDesc r qtid colty fieldIds = do
    fts <- mapM fieldType fieldIds
    return (NConDesc { nc_typeId = qtid,
                       nc_name = qtid,
                       nc_conNo = 0,
                       nc_isStruct = True,
                       nc_isEnum = False,
                       nc_argTypes = fts,
                       nc_fieldIds = fieldIds })
  where
    fieldType fid = do
        fis <- findField r fid
        fi <- find (\ fi -> qualEq (fi_id fi) qtid) fis
        let (_ :>: Forall ks (_ :=> fty)) = fi_assump fi
        (sty, resty) <- splitArrow1 fty
        tsub <- tgenMatch sty colty
        vec <- mapM (\ n -> M.lookup n tsub) [0 .. length ks - 1]
        return (expandSyn (Pred.inst vec resty))

-- | Split exactly one (the outermost) arrow of a type.
splitArrow1 :: Type -> Maybe (Type, Type)
splitArrow1 (TAp (TAp (TCon arr@(TyCon _ _ _)) a) rt)
    | isTConArrow arr = Just (a, rt)
splitArrow1 _ = Nothing

-- | Match a scheme body type (containing TGen) against a concrete type,
-- returning the TGen instantiation.
tgenMatch :: Type -> Type -> Maybe (M.Map Int Type)
tgenMatch (TGen _ n) t = Just (M.singleton n t)
tgenMatch (TAp f a) (TAp f' a') = do
    m1 <- tgenMatch f f'
    m2 <- tgenMatch a a'
    mergeMatch m1 m2
tgenMatch (TCon c) (TCon c') | c == c' = Just M.empty
tgenMatch (TVar v) (TVar v') | v == v' = Just M.empty
tgenMatch _ _ = Nothing

mergeMatch :: M.Map Int Type -> M.Map Int Type -> Maybe (M.Map Int Type)
mergeMatch m1 m2 =
    let both = M.intersectionWith (==) m1 m2
    in  if and (M.elems both) then Just (M.union m1 m2) else Nothing

-- ---------------------------------------------------------------------------
-- Pattern normalization

-- Normalizing yields Nothing when the pattern cannot be understood
-- (unresolved column type, unexpected shape); the whole obligation is
-- then skipped, so unknown situations can never produce false warnings.
-- In particular mixed literals with wildcard digits (4'b1?01) would need
-- mask-aware coverage to analyze correctly (a match can be made complete
-- by masks alone), so their presence abandons the analysis.
normPat :: SymTab -> CType -> CPat -> Maybe NPat
normPat r t p =
    case p of
      CPVar _ -> Just NWild
      CPAny _ -> Just NWild
      CPAs _ p' -> normPat r t p'
      CPMixedLit _ _ _ -> Nothing
      CPLit (CLiteral _ l) ->
          case colKind r t of
            CKLit dom -> do
                k <- litKey l
                -- a literal outside the column's finite domain (a
                -- typecheck-time literal is only range-checked at
                -- elaboration) would break the completeness counting
                case (k, dom) of
                  (LKInt v, LDFinite lo hi _) | v < lo || v > hi -> Nothing
                  _ -> Just (NLit k)
            _ -> Nothing
      CPNegLit (CLiteral _ l) ->
          case colKind r t of
            CKLit dom -> do
                k <- litKey l
                k' <- negLitKey k dom
                Just (NLit k')
            _ -> Nothing
      CPCon1 _ c p' -> normPat r t (CPCon c [p'])
      CPCon c [p1, p2] | c `qualEq` idComma ->
          -- tuple pattern; the column type is (a possibly nested) PrimPair
          case colKind r t of
            CKStruct sd | [t1, t2] <- nc_argTypes sd -> do
                n1 <- normPat r t1 p1
                n2 <- normPat r t2 p2
                Just (NCon sd [n1, n2])
            _ -> Nothing
      CPCon c ps ->
          case colKind r t of
            CKData qtid cons -> do
                cd <- resolveCon r qtid cons c
                payloadTy <- case nc_argTypes cd of
                               [pt] -> Just pt
                               _ -> Nothing
                np <- case ps of
                        [] -> Just NWild
                        [q] -> normPat r payloadTy q
                        _ -> -- positional multi-argument pattern: the
                             -- payload is an anonymous-field SDataCon
                             -- struct
                             normPat r payloadTy
                               (CPstruct (Just True) c (zip tupleIds ps))
                Just (NCon cd [np])
            _ -> Nothing
      CPstruct _ c ips ->
          case colKind r t of
            CKStruct sd -> do
                nps <- normFields r sd ips
                Just (NCon sd nps)
            CKData qtid cons -> do
                -- a constructor with named fields, written in struct form
                cd <- resolveCon r qtid cons c
                payloadTy <- case nc_argTypes cd of
                               [pt] -> Just pt
                               _ -> Nothing
                np <- case colKind r payloadTy of
                        CKStruct psd -> do
                            nps <- normFields r psd ips
                            Just (NCon psd nps)
                        _ -> Nothing
                Just (NCon cd [np])
            _ -> Nothing
      _ -> Nothing

normFields :: SymTab -> NConDesc -> [(Id, CPat)] -> Maybe [NPat]
normFields r sd ips
    -- reject patterns naming fields the struct does not have
    -- (the typechecker rejects them too; this is belt and braces)
    | any (isNothing . structFieldOf . fst) ips = Nothing
    | otherwise = mapM normField (zip (nc_fieldIds sd) (nc_argTypes sd))
  where
    sameField f1 f2 = f1 `qualEq` f2 || unQualId f1 == unQualId f2
    structFieldOf i = find (sameField i) (nc_fieldIds sd)
    normField (fid, fty) =
        case find (sameField fid . fst) ips of
          Just (_, p) -> normPat r fty p
          Nothing -> Just NWild

resolveCon :: SymTab -> Id -> [NConDesc] -> Id -> Maybe NConDesc
resolveCon r qtid cons c = do
    cis <- findCon r c
    ci <- find (\ ci -> qualEq (ci_id ci) qtid) cis
    find (\ cd -> nc_conNo cd == conNo (ci_taginfo ci)) cons

litKey :: Literal -> Maybe LitKey
litKey (LInt il) = Just (LKInt (ilValue il))
litKey (LString s) = Just (LKStr s)
litKey (LChar c) = Just (LKChar c)
litKey (LReal d) = Just (LKReal d)
litKey LPosition = Nothing

-- | The value matched by a negated literal pattern at the column type.
-- Literals whose negation the type does not accept (an elaboration
-- error if the match is ever elaborated) abandon the analysis.
negLitKey :: LitKey -> LitDomain -> Maybe LitKey
negLitKey (LKInt v) (LDFinite lo hi rule) =
    case rule of
      NegWrap maxmag
        | v <= maxmag -> Just (LKInt (negate v `mod` (hi + 1)))
        | otherwise -> Nothing
      NegNone
        | v == 0 -> Just (LKInt 0)
        | otherwise -> Nothing
      NegExact
        | negate v >= lo -> Just (LKInt (negate v))
        | otherwise -> Nothing
negLitKey (LKInt v) LDInfinite = Just (LKInt (negate v))
negLitKey (LKReal d) _ = Just (LKReal (negate d))
negLitKey _ _ = Nothing

-- ---------------------------------------------------------------------------
-- The usefulness analysis

-- Bound on the total number of matrix operations, so that pathological
-- matches degrade to "no warning" instead of blowing up compile time
-- (the analysis is exponential in the worst case, as in GHC).
type Fuel = Int

initialFuel :: Fuel
initialFuel = 100000

-- maximum number of example patterns reported for a non-exhaustive match
maxWitnesses :: Int
maxWitnesses = 4

-- maximum number of literals listed in a "not one of" witness
maxLitsListed :: Int
maxLitsListed = 8

-- | Witness patterns for uncovered values
data WPat = WWild
          | WCon NConDesc [WPat]
          | WLit LitKey
          | WLitOther [LitKey]  -- ^ any value other than these

headCons :: [[NPat]] -> [NConDesc]
headCons rows = nubByConNo [cd | (NCon cd _ : _) <- rows]
  where nubByConNo = foldr (\ cd acc ->
                             if any (\ cd' -> nc_conNo cd' == nc_conNo cd) acc
                             then acc else cd : acc) []

headLits :: [[NPat]] -> [LitKey]
headLits rows = nub [k | (NLit k : _) <- rows]

specCon :: NConDesc -> [[NPat]] -> [[NPat]]
specCon cd rows =
    [ args ++ ps | (NCon cd' args : ps) <- rows, nc_conNo cd' == nc_conNo cd ]
    ++ [ replicate arity NWild ++ ps | (NWild : ps) <- rows ]
  where arity = length (nc_argTypes cd)

specLit :: LitKey -> [[NPat]] -> [[NPat]]
specLit k rows =
    [ ps | (NLit k' : ps) <- rows, k' == k ]
    ++ [ ps | (NWild : ps) <- rows ]

defaultMat :: [[NPat]] -> [[NPat]]
defaultMat rows = [ ps | (NWild : ps) <- rows ]

litDomainSize :: LitDomain -> Maybe Integer
litDomainSize (LDFinite lo hi _) = Just (hi - lo + 1)
litDomainSize LDInfinite = Nothing

-- the smallest value in a finite domain not present in the given set
smallestMissing :: Integer -> Integer -> [LitKey] -> Integer
smallestMissing lo hi ks =
    let covered = S.fromList [ v | LKInt v <- ks ]
        go v | v > hi = lo  -- unreachable when called on incomplete domains
             | v `S.member` covered = go (v + 1)
             | otherwise = v
    in  go lo

-- | Compute (up to maxWitnesses+1) examples of value vectors not covered
-- by the guard-free rows.  Nothing means the fuel ran out.
uncovered :: SymTab -> Fuel -> [CType] -> [[NPat]] -> (Fuel, Maybe [[WPat]])
uncovered r fuel _ _ | fuel <= 0 = (fuel, Nothing)
uncovered r fuel ts [] =
    -- nothing covers anything: everything is a witness
    (fuel - 1, Just [replicate (length ts) WWild])
uncovered r fuel [] rows = (fuel - 1, Just [])
uncovered r fuel (t : ts) rows =
    case colKind r t of
      CKData _ cons
        | sigComplete cons -> perCon (fuel - 1) cons []
        | otherwise ->
            -- witnesses with the missing constructors first, then keep
            -- looking inside the constructors that are present
            let missing = [ cd | cd <- cons, notPresent cd ]
                wits = if null present
                       then [WWild]
                       else [ WCon cd (replicate (length (nc_argTypes cd)) WWild)
                            | cd <- missing ]
            in  thenPerCon (prefixDefault (fuel - 1) wits) present
      CKStruct sd -> perCon (fuel - 1) [sd] []
      CKLit dom ->
          let lits = headLits rows
          in  case litDomainSize dom of
                Just size | genericLength lits == size ->
                    perLit (fuel - 1) lits []
                _ ->
                    let wit = case dom of
                                _ | null lits -> WWild
                                LDFinite lo hi _ ->
                                    WLit (LKInt (smallestMissing lo hi lits))
                                LDInfinite -> WLitOther lits
                    in  thenPerLit (prefixDefault (fuel - 1) [wit]) lits
      CKOpaque
        | all wildHead rows -> prefixDefault (fuel - 1) [WWild]
        | otherwise -> (fuel - 1, Just [])  -- can't analyze: assume covered
  where
    present = headCons rows
    notPresent cd = all (\ cd' -> nc_conNo cd' /= nc_conNo cd) present
    sigComplete cons = all (\ cd -> not (notPresent cd)) cons
    wildHead (NWild : _) = True
    wildHead _ = False
    cap ws = take (maxWitnesses + 1) ws
    -- specialize per constructor, wrapping witnesses back up
    perCon f [] acc = (f, Just (cap acc))
    perCon f (cd : cds) acc
      | length acc > maxWitnesses = (f, Just (cap acc))
      | otherwise =
        let arity = length (nc_argTypes cd)
            (f', mws) = uncovered r f (nc_argTypes cd ++ ts) (specCon cd rows)
        in  case mws of
              Nothing -> (f', Nothing)
              Just ws ->
                  perCon f' cds
                      (acc ++ [ WCon cd (take arity w) : drop arity w
                              | w <- ws ])
    perLit f [] acc = (f, Just (cap acc))
    perLit f (k : ks) acc
      | length acc > maxWitnesses = (f, Just (cap acc))
      | otherwise =
        let (f', mws) = uncovered r f ts (specLit k rows)
        in  case mws of
              Nothing -> (f', Nothing)
              Just ws -> perLit f' ks (acc ++ [ WLit k : w | w <- ws ])
    prefixDefault f wits =
        let (f', mws) = uncovered r f ts (defaultMat rows)
        in  case mws of
              Nothing -> (f', Nothing)
              Just ws -> (f', Just (cap [ wit : w | w <- ws, wit <- wits ]))
    thenPerCon (f, Nothing) _ = (f, Nothing)
    thenPerCon (f, Just acc) cds
      | length acc > maxWitnesses = (f, Just (cap acc))
      | otherwise = perCon f cds acc
    thenPerLit (f, Nothing) _ = (f, Nothing)
    thenPerLit (f, Just acc) ks
      | length acc > maxWitnesses = (f, Just (cap acc))
      | otherwise = perLit f ks acc

-- | Is the vector qs useful w.r.t. the rows (can it match something the
-- rows do not)?  Nothing means the fuel ran out.
useful :: SymTab -> Fuel -> [CType] -> [[NPat]] -> [NPat] -> (Fuel, Maybe Bool)
useful r fuel _ _ _ | fuel <= 0 = (fuel, Nothing)
useful r fuel [] rows [] = (fuel - 1, Just (null rows))
useful r fuel [] _ _ = (fuel - 1, Just True)  -- shape mismatch: be quiet
useful r fuel _ _ [] = (fuel - 1, Just True)
useful r fuel (t : ts) rows (q : qs) =
    case q of
      NCon cd args ->
          useful r (fuel - 1) (nc_argTypes cd ++ ts) (specCon cd rows)
                 (args ++ qs)
      NLit k -> useful r (fuel - 1) ts (specLit k rows) qs
      NWild ->
          case colKind r t of
            CKData _ cons
              | sigComplete cons -> anyCon (fuel - 1) cons
              | otherwise -> useful r (fuel - 1) ts (defaultMat rows) qs
            CKStruct sd -> anyCon (fuel - 1) [sd]
            CKLit dom ->
                let lits = headLits rows
                in  case litDomainSize dom of
                      Just size | genericLength lits == size ->
                          anyLit (fuel - 1) lits
                      _ -> useful r (fuel - 1) ts (defaultMat rows) qs
            CKOpaque -> useful r (fuel - 1) ts (defaultMat rows) qs
  where
    present = headCons rows
    sigComplete cons =
        all (\ cd -> any (\ cd' -> nc_conNo cd' == nc_conNo cd) present) cons
    anyCon f [] = (f, Just False)
    anyCon f (cd : cds) =
        let arity = length (nc_argTypes cd)
            (f', mu) = useful r f (nc_argTypes cd ++ ts) (specCon cd rows)
                              (replicate arity NWild ++ qs)
        in  case mu of
              Nothing -> (f', Nothing)
              Just True -> (f', Just True)
              Just False -> anyCon f' cds
    anyLit f [] = (f, Just False)
    anyLit f (k : ks) =
        let (f', mu) = useful r f ts (specLit k rows) qs
        in  case mu of
              Nothing -> (f', Nothing)
              Just True -> (f', Just True)
              Just False -> anyLit f' ks

-- ---------------------------------------------------------------------------
-- Witness rendering
--
-- Hand-rolled rather than reusing the CPat pretty-printers, so that the
-- examples read like the patterns a user would actually write (no
-- "tagged" on enum tags in BSV, wildcards for omitted struct fields, etc.)

isAnonFields :: NConDesc -> Bool
isAnonFields cd =
    and (zipWith qualEq (nc_fieldIds cd) tupleIds)

isUnitType :: CType -> Bool
isUnitType t = case leftCon t of
                 Just i -> qualEq i idPrimUnit
                 Nothing -> False

isWWild :: WPat -> Bool
isWWild WWild = True
isWWild _ = False

showLitKey :: LitKey -> String
showLitKey (LKInt v) = show v
showLitKey (LKStr s) = show s
showLitKey (LKChar c) = show c
showLitKey (LKReal d) = show d

-- collapse right-nested pairs, so tuple witnesses print as (a, b, c)
tupleElems :: NConDesc -> [WPat] -> [WPat]
tupleElems cd [w1, w2]
    | nc_typeId cd `qualEq` idPrimPair =
        case w2 of
          WCon cd' ws' | nc_isStruct cd', nc_typeId cd' `qualEq` idPrimPair ->
              w1 : tupleElems cd' ws'
          _ -> [w1, w2]
tupleElems _ ws = ws

commaJoin :: [String] -> String
commaJoin [] = ""
commaJoin ss = foldr1 (\ a b -> a ++ ", " ++ b) ss

showWitness :: Bool -> [WPat] -> String
showWitness classic ws = unwords (map (showW False) ws)
  where
    wild = if classic then "_" else ".*"
    showW _ WWild = wild
    showW _ (WLit k) = showLitKey k
    showW _ (WLitOther ks) =
        let shown = map showLitKey (take maxLitsListed ks)
            more = if length ks > maxLitsListed then ", ..." else ""
        in  "v when v is not one of {" ++ commaJoin shown ++ more ++ "}"
    showW nested (WCon cd ws')
        | nc_isStruct cd = showStruct cd ws'
        | otherwise = showCon nested cd ws'
    conName cd = getIdBaseString (nc_name cd)
    -- a constructor and its single payload
    showCon nested cd ws' =
        let payload = case ws' of
                        [w] -> w
                        _ -> WWild
            noArg = case nc_argTypes cd of
                      [pt] -> isUnitType pt
                      _ -> True
            -- BSV writes union members as "tagged Name", but enum tags bare
            tag = if classic || nc_isEnum cd then "" else "tagged "
            body
              | noArg = tag ++ conName cd
              | otherwise =
                  case payload of
                    WCon sd fws | nc_isStruct sd, isAnonFields sd,
                                  not (null (nc_fieldIds sd)) ->
                        -- positional constructor arguments
                        tag ++ conName cd ++ " " ++
                        unwords (map (showW True) fws)
                    WCon sd fws | nc_isStruct sd,
                                  not (nc_typeId sd `qualEq` idPrimPair),
                                  not (null (nc_fieldIds sd)) ->
                        -- named fields
                        tag ++ conName cd ++ " " ++ showFields (fieldPats sd fws)
                    _ -> tag ++ conName cd ++ " " ++ showW True payload
            -- parenthesize nested constructor patterns: in Classic only
            -- when there is a payload, in BSV any nested "tagged"
            needParen = nested && (if classic then not noArg
                                   else not (null tag))
        in  if needParen then "(" ++ body ++ ")" else body
    showStruct cd ws'
      | nc_typeId cd `qualEq` idPrimPair =
          let es = tupleElems cd ws'
              open = if classic then "(" else "{"
              close = if classic then ")" else "}"
          in  open ++ commaJoin (map (showW False) es) ++ close
      | null (nc_fieldIds cd) = if classic then "()" else "{}"
      | otherwise =
          getIdBaseString (nc_typeId cd) ++ " " ++
          showFields (fieldPats cd ws')
    -- only show the interesting (non-wildcard) fields, unless that
    -- would show nothing at all
    fieldPats cd ws' =
        let named = zip (nc_fieldIds cd) ws'
            interesting = [ nw | nw@(_, w) <- named, not (isWWild w) ]
        in  if null interesting then take 1 named else interesting
    showFields fps =
        let sep = if classic then " = " else ": "
        in  "{ " ++
            commaJoin [ getIdBaseString f ++ sep ++ showW False w
                      | (f, w) <- fps ] ++ " }"

-- ---------------------------------------------------------------------------
-- The checker

describeCtx :: PatMatchContext -> String
describeCtx PMCase = "this case expression"
describeCtx (PMDef i)
    | isBadId i || isRenamingId i = "this pattern match"
    | base == "_lam" = "this lambda expression"
    | otherwise = "the clauses for `" ++ displayName ++ "'"
  where
    base = getIdBaseString i
    -- instance methods are internally prefixed with an underscore
    displayName = case base of
                    ('_' : rest@(_:_)) -> rest
                    _ -> base

-- | Check one obligation, producing warnings for non-exhaustive matching
-- and redundant arms.  Runs after typechecking of the enclosing top-level
-- definition has succeeded, with the final substitution applied to
-- 'pmo_type'.
checkPatMatches :: Flags -> SymTab -> PatMatchObligation -> [WMsg]
checkPatMatches flags r o
    | not doIncomplete && not doOverlap = []
    | length colTypes < pmo_ncols o = []
    | otherwise =
        case mapM normRow (pmo_rows o) of
          Nothing -> []  -- something we cannot analyze; stay quiet
          Just nrows -> incompleteWarnings nrows ++ redundantWarnings nrows
  where
    doIncomplete = warnIncompletePatterns flags
    doOverlap = warnOverlappingPatterns flags
    ctxStr = describeCtx (pmo_ctx o)
    (argTypes, _) = getArrows (pmo_type o)
    colTypes = take (pmo_ncols o) argTypes

    normRow row = do
        nps <- mapM (uncurry (normPat r)) (zip colTypes (pmr_pats row))
        return (row, nps, pmr_guarded row)

    coverMatrix nrows = [ nps | (_, nps, guarded) <- nrows, not guarded ]

    incompleteWarnings nrows
      | not doIncomplete = []
      | otherwise =
        case snd (uncovered r initialFuel colTypes (coverMatrix nrows)) of
          Just ws@(_:_) ->
              let shown = map (showWitness (isClassic ()))
                              (take maxWitnesses ws)
                  truncated = length ws > maxWitnesses
              in  [(pmo_pos o, WNonExhaustivePattern ctxStr shown truncated)]
          _ -> []

    redundantWarnings nrows
      | not doOverlap = []
      | otherwise = go initialFuel [] nrows
      where
        go _ _ [] = []
        go fuel prior ((row, nps, guarded) : rest)
          | fuel <= 0 = []
          | pmr_gen_dflt row = go fuel prior' rest
          | otherwise =
              case useful r fuel colTypes prior nps of
                (fuel', Just False) ->
                    (pmr_pos row,
                     WRedundantPattern ctxStr (showRow row))
                    : go fuel' prior' rest
                (fuel', _) -> go fuel' prior' rest
          where
            -- only guard-free rows can shadow later rows
            prior' = if guarded then prior else prior ++ [nps]
        showRow row = unwords (map (pfpString) (pmr_pats row))
