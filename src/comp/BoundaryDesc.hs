module BoundaryDesc(
                    BoundaryEntryR(..),
                    CodecRef(..),
                    boundaryIdForIfc,
                    readBoundaryEntries,
                    shadowBoundaryErrs,
                    codecShadowErrs,
                    wrapperCodecs
                   ) where

import qualified Data.Map as M
import Data.Char(isAlphaNum)

import Id
import PreIds(idBuildUndef, idFromWrapField)
import Position(noPosition)
import FStringCompat(mkFString, getFString)
import ISyntax
import ISyntaxSubst(tSubst)
import VModInfo(VFieldInfo(..))
import SymTab(SymTab, findType, findSClass, TypeInfo(..))
import CType(TISort(..), CTypeclass(..))
import Pred(Class(..))
import Pragma(PProp, isAlwaysRdy)
import Prim(PrimOp(..))
import PPrint(ppReadable)
import ContractCheck(whead, readStr1, readListSpine, readPairWith)

-- ==================================================
-- Reading boundary_<flatifc> defs -- the codec-bearing sibling of the
-- signature def.  A field entry is an application of primMkFieldEntry
-- whose WrapField dictionary was resolved by the typechecker at the
-- declaration; the dictionary reference (a named def, with its
-- instantiation types and resolved body) is the leaf's codec.  Opaque
-- entries (clock/reset/inout) are the native floor: no dictionary.

-- a reference to a leaf's marshalling dictionary
data CodecRef a = CodecRef {
        cr_name  :: Maybe Id,   -- the referenced def, when the
                                -- dictionary resolves to a named def
                                -- (an instance at concrete types);
                                -- Nothing for an in-line construction
        cr_types :: [IType],    -- the instantiation [name, f, w]
        cr_body  :: IExpr a     -- the resolved dictionary expression
    }

data BoundaryEntryR a
  = BFieldR {
        bf_path  :: String,             -- flattened leaf path
        bf_slots :: [(String, String)], -- kind/type/prefix/result/argN
        bf_ftype :: Maybe IType,        -- the leaf's resolved method
                                        -- type, from the f-typed
                                        -- proxy the typechecker
                                        -- instantiated (increment 9)
        bf_codec :: CodecRef a
    }
  | BOpaqueR {
        bo_path :: String,
        bo_kind :: String,              -- "clock" | "reset" | "inout"
        bo_slots :: [(String, String)]  -- path/kind/prefix/result
    }

-- the (package-qualified) id of an interface's compiler-emitted
-- boundary def, from the FLAT interface id (whose gen suffix
-- sanitizes to the trailing underscore), matching GenWrap's
-- mkBoundaryDef exactly
boundaryIdForIfc :: Id -> Id
boundaryIdForIfc ifcId =
    let sane c = if isAlphaNum c then c else '_'
        base = "boundary_" ++ map sane (getIdBaseString ifcId)
    in  setIdBase ifcId (mkFString base)

-- like whead, but keeping the type arguments accumulated along the
-- application spine (innermost first); no lambda-stepping -- the
-- callers apply it to direct applications only
headTypes :: M.Map Id (IExpr a) -> IExpr a ->
             (IExpr a, [IType], [IExpr a])
headTypes env e0 = go env e0 [] []
  where
    go env' (IAps f ts es) tss as = go env' f (ts ++ tss) (es ++ as)
    go env' (IVar v) tss as | Just d <- M.lookup v env' = go env' d tss as
    go _ h tss as = (h, tss, as)

-- fully inline an environment's bindings into an expression, making
-- it self-contained (dictionary trees are small and ground; the fuel
-- bounds variable-chain loops, which cannot arise from letseq but
-- guard against malformed input)
expandVars :: Int -> M.Map Id (IExpr a) -> IExpr a ->
              Either String (IExpr a)
expandVars n env e0 =
    case e0 of
      IVar v | Just d <- M.lookup v env ->
                 if n <= 0
                 then Left "dictionary expansion out of fuel"
                 else expandVars (n - 1) env d
             | otherwise -> Right e0
      IAps f ts es ->
          do f' <- expandVars n env f
             es' <- mapM (expandVars n env) es
             return (IAps f' ts es')
      ILam v t b ->
          ILam v t `fmap` expandVars n (M.delete v env) b
      ILAM v k b ->
          ILAM v k `fmap` expandVars n env b
      _ -> Right e0

-- structural equality of dictionary trees, modulo positions, the
-- bodies behind ICDef references (a same-package reference carries
-- the real body, a cross-package one an undet placeholder -- the
-- def Id is the identity), and application-spine nesting (compared
-- through the headTypes-normalized view).  A node of an
-- EVIDENCE-ONLY class (no methods -- numeric evidence like
-- TupleSize) compares by its fully-applied dictionary type alone:
-- different compiles legitimately construct such dictionaries
-- differently (a structural ICTuple vs the source instance chain,
-- the b1356 finding), and with no methods the construction is
-- observationally irrelevant
dictEq :: (IType -> Bool) -> IExpr a -> IExpr a -> Bool
dictEq evOnly a b =
    let (ha, tsa, esa) = headTypes M.empty a
        (hb, tsb, esb) = headTypes M.empty b
        strict = headEq ha hb && tsa == tsb &&
                 length esa == length esb &&
                 and (zipWith (dictEq evOnly) esa esb)
        evid = case (appliedTy ha tsa esa, appliedTy hb tsb esb) of
                 (Just ta, Just tb) -> ta == tb && evOnly ta
                 _ -> False
    in  strict || evid
  where
    appliedTy (ICon _ ci) ts es =
        do t <- itInst (iConType ci) ts
           dropArrs (length es) t
    appliedTy _ _ _ = Nothing
    itInst t [] = Just t
    itInst (ITForAll v _ r) (t:ts) = itInst (tSubst v t r) ts
    itInst _ _ = Nothing
    dropArrs :: Int -> IType -> Maybe IType
    dropArrs 0 t = Just t
    dropArrs n (ITAp (ITAp arr _) r) | arr == itArrow =
        dropArrs (n - 1) r
    dropArrs _ _ = Nothing
    headEq (ICon i1 c1) (ICon i2 c2) = i1 == i2 && conEq c1 c2
    headEq (IVar v1) (IVar v2) = v1 == v2
    headEq _ _ = False
    conEq (ICDef {}) (ICDef {}) = True
    conEq (ICValue {}) (ICValue {}) = True
    conEq (ICDef {}) (ICValue {}) = True
    conEq (ICValue {}) (ICDef {}) = True
    conEq (ICSel { selNo = n1, numSel = m1 })
          (ICSel { selNo = n2, numSel = m2 }) = n1 == n2 && m1 == m2
    conEq (ICPrim { primOp = p1 }) (ICPrim { primOp = p2 }) = p1 == p2
    conEq (ICString { iStr = s1 }) (ICString { iStr = s2 }) = s1 == s2
    conEq (ICInt { iVal = v1 }) (ICInt { iVal = v2 }) = v1 == v2
    conEq (ICUndet { iConType = t1 }) (ICUndet { iConType = t2 }) =
        t1 == t2
    conEq (ICCon { conTagInfo = c1 }) (ICCon { conTagInfo = c2 }) =
        c1 == c2
    conEq (ICTuple {}) (ICTuple {}) = True
    conEq _ _ = False

-- is this fully-applied dictionary type of a class with NO methods
-- (evidence-only)?  The class-dictionary struct's fields are its
-- methods plus one slot per superclass; methodless means the field
-- count does not exceed the superclass count.
evOnlyClassTy :: SymTab -> IType -> Bool
evOnlyClassTy symt t0 =
    case itLeftCon t0 of
      Just ci ->
          case (findType symt ci, findSClass symt (CTypeclass ci)) of
            (Just (TypeInfo _ _ _ (TIstruct _ fs) _), Just cls) ->
                length fs <= length (super cls)
            _ -> False
      Nothing -> False
  where
    itLeftCon (ITAp f _) = itLeftCon f
    itLeftCon (ITCon ci _ _) = Just ci
    itLeftCon _ = Nothing

readBoundaryEntries :: IExpr a -> Either String [BoundaryEntryR a]
readBoundaryEntries = readListSpine malformed readEntry M.empty
  where
    malformed :: Either String b
    malformed = Left "malformed boundary def"

    readEntry env e =
      case whead env e of
        (env', ICon _ (ICPrim { primOp = PrimMkOpaqueEntry }),
               [p, k, slotsE]) ->
            do path <- readStr1 malformed env' p
               kind <- readStr1 malformed env' k
               slots <- readListSpine malformed readSlot env' slotsE
               return (BOpaqueR { bo_path = path, bo_kind = kind,
                                  bo_slots = slots })
        (env', ICon _ (ICPrim { primOp = PrimMkFieldEntry }), as) ->
            -- the application is (dict, name proxy, type proxy,
            -- slots): the resolved WrapField dictionary comes first,
            -- the proxies are type-level (unreadable as values), and
            -- the leaf's path travels as the first slot
            case as of
              [dict, _nmProxy, fProxy, slotsE] ->
                  do slots <- readListSpine malformed readSlot env' slotsE
                     path <- case lookup "path" slots of
                               Just str -> Right str
                               Nothing -> malformed
                     let (_denv, dhead, _dargs) = whead env' dict
                         nm = case dhead of
                                ICon i (ICDef {}) -> Just i
                                ICon i (ICValue {}) -> Just i
                                _ -> Nothing
                         -- the proxy is (CAny :: f) at the
                         -- declaration; iConv renders it as
                         -- primBuildUndefined applied AT the field's
                         -- method type (buildUndef, IConv.hs), so
                         -- the type is the application's type
                         -- argument -- kept by headTypes, which
                         -- whead would discard
                         mft = case headTypes env' fProxy of
                                 (ICon i _, [t], _)
                                   | i == idBuildUndef -> Just t
                                 (ICon _ (ICUndet { iConType = t }),
                                  _, _) -> Just t
                                 _ -> Nothing
                     -- record the codec self-contained: the entry's
                     -- dictionary argument may be a let-bound
                     -- variable of the description def; inline the
                     -- reading environment into it (increment 10)
                     dict' <- expandVars 200 env' dict
                     return (BFieldR { bf_path = path,
                                       bf_slots = slots,
                                       bf_ftype = mft,
                                       bf_codec = CodecRef {
                                           cr_name = nm,
                                           cr_types = [],
                                           cr_body = dict' } })
              _ -> malformed
        _ -> malformed

    readSlot env e =
      readPairWith malformed
        (\ env' k v ->
           do sk <- readStr1 malformed env' k
              sv <- readStr1 malformed env' v
              return (sk, sv))
        env e

-- ==================================================
-- The codec shadow (increment 10): does the description's recorded
-- codec EQUAL the dictionary the wrapper's own compilation re-solved?
-- The compiled wrapper definition applies the fromWrapField class
-- method once per boundary leaf (dictionary first, per IConv's field
-- application shape); its let-bound dictionaries are applied-lambda
-- shapes, collected into one environment (letseq freshness makes the
-- flat map sound) and inlined before comparison.

-- every (leaf name, fully-inlined dictionary) pair in a compiled
-- wrapper body (two accumulator-style passes: collect the let
-- bindings, then the fromWrapField applications)
wrapperCodecs :: IExpr a -> [(String, Either String (IExpr a))]
wrapperCodecs wbody =
    let binds = M.fromList (lets wbody [])

        lets e acc = case e of
                       IAps (ILam v _ b) _ [rhs] ->
                           (v, rhs) : lets b (lets rhs acc)
                       IAps f _ es -> lets f (foldr lets acc es)
                       ILam _ _ b -> lets b acc
                       ILAM _ _ b -> lets b acc
                       _ -> acc

        uses e acc = case e of
                       IAps (ICon i (ICSel {})) (ITStr s : _) (d : _)
                         | i == idFromWrapField ->
                           (getFString s, expandVars 200 binds d)
                               : deeper e acc
                       _ -> deeper e acc
        deeper e acc = case e of
                         IAps f _ es -> uses f (foldr uses acc es)
                         ILam _ _ b -> uses b acc
                         ILAM _ _ b -> uses b acc
                         _ -> acc
    in  uses wbody []

-- compare a compiled wrapper's codecs against the description's:
-- every fromWrapField dictionary must be structurally identical to
-- the recorded CodecRef of the entry with that leaf name (vector
-- leaves share one parametric entry, so several uses may check
-- against the same recorded codec); opaque leaves (clock, reset,
-- inout) have no recorded codec and are skipped
codecShadowErrs :: SymTab -> [BoundaryEntryR a] ->
                   [(String, Either String (IExpr a))] -> [String]
codecShadowErrs symt entries pairs =
    let evOnly = evOnlyClassTy symt
        recorded = [ (bf_path e, cr_body (bf_codec e))
                   | e@(BFieldR {}) <- entries ]
        opaque = [ bo_path e | e@(BOpaqueR {}) <- entries ]
    in  [ err
        | (nm, mdict) <- pairs,
          nm `notElem` opaque,
          err <- case (lookup nm recorded, mdict) of
                   (Nothing, _) ->
                       ["codec applied for `" ++ nm ++
                        "', which no entry describes"]
                   (_, Left msg) ->
                       ["codec of `" ++ nm ++ "': " ++ msg]
                   (Just rec_d, Right got_d)
                     | dictEq evOnly rec_d got_d -> []
                     | otherwise ->
                         ["codec of `" ++ nm ++ "' differs from the " ++
                          "description's recorded dictionary\n" ++
                          "  recorded: " ++ ppReadable rec_d ++
                          "  re-solved: " ++ ppReadable got_d] ]

-- ==================================================
-- The shadow check (increment 6): does the description determine the
-- boundary?  Given the module's effective pragmas, the description's
-- entries, and the veriFields the wrapper actually assembled, report
-- every disagreement.  This v1 compares the member inventory --
-- names, kinds, ready-twin presence (after the effective collapse),
-- enable and output presence per kind -- and leaves port-name
-- equality to the fold increment.

shadowBoundaryErrs :: [PProp] -> [BoundaryEntryR a] -> [VFieldInfo]
                   -> [String]
shadowBoundaryErrs pps entries fields =
    let -- a described path renders to the boundary with dots joined
        -- as underscores; a vector position renders as `[_]' in the
        -- description (one parametric entry, one shared codec, per
        -- the WrapField index-erasure upstream) but as a concrete
        -- index at the boundary.  Match parametrically; whether the
        -- boundary has the RIGHT NUMBER of indices is not yet
        -- description data (A97 aggregate clauses).
        comps = foldr split [""]
          where split '.' acc = "" : acc
                split c (h:t) = (c:h) : t
                split _ [] = [""]
        matchPath dpath aname =
            go (comps dpath) aname
          where
            go [] rest = null rest
            go (d:ds) rest =
                case d of
                  "[_]" -> or [ stepSep ds rest'
                              | (idx, rest') <- splitsOf rest,
                                not (null idx), all isDigitC idx ]
                  _ -> case stripPre d rest of
                         Just rest' -> stepSep ds rest'
                         Nothing -> False
            stepSep [] rest = null rest
            stepSep ds rest = case rest of
                                ('_':rest') -> go ds rest'
                                _ -> False
            splitsOf str = [ (take k str, drop k str) | k <- [1 .. length str] ]
            stripPre pre str = let n = length pre
                               in  if take n str == pre
                                   then Just (drop n str) else Nothing
            isDigitC c = c >= '0' && c <= '9'

        -- expected method leaves (described paths) and their kinds
        methEnts = [ (bf_path e, kindOf e) | e@(BFieldR {}) <- entries ]
        kindOf e = case lookup "kind" (bf_slots e) of
                     Just k -> k
                     Nothing -> "value"

        rdyName m = getIdBaseString (mkRdyId (mk_dangling_id m noPosition))

        -- does an assembled method name match a described leaf (or
        -- its ready twin, when the effective pragmas keep it)?
        matchesLeaf aname =
            [ k | (d, k) <- methEnts, matchPath d aname ]
        matchesRdy aname =
            case stripRdy aname of
              Just base ->
                  not (null (matchesLeaf base)) &&
                  not (isAlwaysRdy pps (mkRdyId (mk_dangling_id base noPosition)))
              Nothing -> False
        stripRdy a = let rdy = rdyName "" -- "RDY_"
                         n = length rdy
                     in  if take n a == rdy then Just (drop n a) else Nothing
        expClks  = [ bo_path e | e@(BOpaqueR {}) <- entries,
                     bo_kind e == "clock" ]
        expRsts  = [ bo_path e | e@(BOpaqueR {}) <- entries,
                     bo_kind e == "reset" ]
        expInos  = [ bo_path e | e@(BOpaqueR {}) <- entries,
                     bo_kind e == "inout" ]

        actMeths = [ getIdBaseString n | Method { vf_name = n } <- fields ]
        actClks  = [ getIdBaseString n | Clock { vf_name = n } <- fields ]
        actRsts  = [ getIdBaseString n | Reset { vf_name = n } <- fields ]
        actInos  = [ getIdBaseString n | Inout { vf_name = n } <- fields ]

        -- every assembled method must match a described leaf or a
        -- kept ready twin; every described leaf must cover at least
        -- one assembled method
        extraMeths =
            [ "method `" ++ a ++ "' assembled but not described"
            | a <- actMeths,
              null (matchesLeaf a), not (matchesRdy a) ]
        missingMeths =
            [ "method `" ++ d ++ "' described but not assembled"
            | (d, _) <- methEnts,
              not (or [ matchPath d a | a <- actMeths ]) ]

        -- opaque members (clocks, resets, inouts) match their
        -- described paths parametrically, like methods
        missing what exp act =
            [ what ++ " `" ++ d ++ "' described but not assembled"
            | d <- exp, not (or [ matchPath d a | a <- act ]) ]
        extra what exp act =
            [ what ++ " `" ++ a ++ "' assembled but not described"
            | a <- act, not (or [ matchPath d a | d <- exp ]) ]

        -- per-kind port shape for the leaves present on both sides
        shapeErrs =
            [ err
            | Method { vf_name = n, vf_enable = en, vf_output = out }
                  <- fields,
              k : _ <- [matchesLeaf (getIdBaseString n)],
              err <- let hasEn = maybe False (const True) en
                         hasOut = maybe False (const True) out
                         m = getIdBaseString n
                     -- output-port presence is deliberately not
                     -- required: a zero-width result drops its port
                     -- (the floor's empty member), and widths are not
                     -- description data
                     in case k of
                          "action" ->
                              [ "method `" ++ m ++ "': action without an enable"
                              | not hasEn ] ++
                              [ "method `" ++ m ++ "': action with an output"
                              | hasOut ]
                          "actionvalue" ->
                              [ "method `" ++ m ++ "': actionvalue without an enable"
                              | not hasEn ]
                          -- "value" is the emission's catch-all: a
                          -- method type GenWrap cannot classify
                          -- pre-typecheck (a type-function type, the
                          -- #313/#383 hole) also lands here, so the
                          -- fallback kind asserts nothing
                          _ -> [] ]
    in  missingMeths ++
        extraMeths ++
        missing "clock" expClks actClks ++
        extra "clock" expClks actClks ++
        missing "reset" expRsts actRsts ++
        extra "reset" expRsts actRsts ++
        missing "inout" expInos actInos ++
        extra "inout" expInos actInos ++
        shapeErrs
