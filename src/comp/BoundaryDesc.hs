module BoundaryDesc(
                    BoundaryEntryR(..),
                    CodecRef(..),
                    boundaryIdForIfc,
                    readBoundaryEntries,
                    shadowBoundaryErrs
                   ) where

import qualified Data.Map as M
import Data.Char(isAlphaNum)

import Data.List((\\))

import Id
import Position(noPosition)
import FStringCompat(mkFString)
import ISyntax
import VModInfo(VFieldInfo(..))
import Pragma(PProp, isAlwaysRdy)
import Prim(PrimOp(..))
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
              [dict, _nmProxy, _fProxy, slotsE] ->
                  do slots <- readListSpine malformed readSlot env' slotsE
                     path <- case lookup "path" slots of
                               Just str -> Right str
                               Nothing -> malformed
                     let (_denv, dhead, _dargs) = whead env' dict
                         nm = case dhead of
                                ICon i (ICDef {}) -> Just i
                                ICon i (ICValue {}) -> Just i
                                _ -> Nothing
                     return (BFieldR { bf_path = path,
                                       bf_slots = slots,
                                       bf_codec = CodecRef {
                                           cr_name = nm,
                                           cr_types = [],
                                           cr_body = dict } })
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
