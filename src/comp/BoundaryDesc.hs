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
        bo_kind :: String               -- "clock" | "reset" | "inout"
    }

-- the (package-qualified) id of an interface's compiler-emitted
-- boundary def: named after the flattened interface, sanitized
-- exactly as GenWrap's mkBoundaryDef does
boundaryIdForIfc :: Id -> Id
boundaryIdForIfc ifcId =
    let sane c = if isAlphaNum c then c else '_'
        base = "boundary_" ++ map sane (getIdBaseString ifcId ++ "_")
    in  setIdBase ifcId (mkFString base)

readBoundaryEntries :: IExpr a -> Either String [BoundaryEntryR a]
readBoundaryEntries = readListSpine malformed readEntry M.empty
  where
    malformed :: Either String b
    malformed = Left "malformed boundary def"

    readEntry env e =
      case whead env e of
        (env', ICon _ (ICPrim { primOp = PrimMkOpaqueEntry }), [p, k]) ->
            do path <- readStr1 malformed env' p
               kind <- readStr1 malformed env' k
               return (BOpaqueR { bo_path = path, bo_kind = kind })
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
    let dotsToUnders = map (\ c -> if c == '.' then '_' else c)

        -- expected method leaves (underscore rendering) and their kinds
        methEnts = [ (dotsToUnders (bf_path e), kindOf e)
                   | e@(BFieldR {}) <- entries ]
        kindOf e = case lookup "kind" (bf_slots e) of
                     Just k -> k
                     Nothing -> "value"

        -- a method's ready twin is expected unless the effective
        -- pragmas collapse it
        expRdys = [ rdyName m | (m, _) <- methEnts,
                    not (isAlwaysRdy pps (mkRdyId (mk_dangling_id m noPosition))) ]
        rdyName m = getIdBaseString (mkRdyId (mk_dangling_id m noPosition))

        expMeths = map fst methEnts ++ expRdys
        expClks  = [ bo_path e | e@(BOpaqueR {}) <- entries,
                     bo_kind e == "clock" ]
        expRsts  = [ bo_path e | e@(BOpaqueR {}) <- entries,
                     bo_kind e == "reset" ]
        expInos  = [ dotsToUnders (bo_path e) | e@(BOpaqueR {}) <- entries,
                     bo_kind e == "inout" ]

        actMeths = [ getIdBaseString n | Method { vf_name = n } <- fields ]
        actClks  = [ getIdBaseString n | Clock { vf_name = n } <- fields ]
        actRsts  = [ getIdBaseString n | Reset { vf_name = n } <- fields ]
        actInos  = [ getIdBaseString n | Inout { vf_name = n } <- fields ]

        missing what exp act =
            [ what ++ " `" ++ x ++ "' described but not assembled"
            | x <- exp \\ act ]
        extra what exp act =
            [ what ++ " `" ++ x ++ "' assembled but not described"
            | x <- act \\ exp ]

        -- per-kind port shape for the leaves present on both sides
        shapeErrs =
            [ err
            | Method { vf_name = n, vf_enable = en, vf_output = out }
                  <- fields,
              Just k <- [lookup (getIdBaseString n) methEnts],
              err <- let hasEn = maybe False (const True) en
                         hasOut = maybe False (const True) out
                         m = getIdBaseString n
                     in case k of
                          "action" ->
                              [ "method `" ++ m ++ "': action without an enable"
                              | not hasEn ] ++
                              [ "method `" ++ m ++ "': action with an output"
                              | hasOut ]
                          "actionvalue" ->
                              [ "method `" ++ m ++ "': actionvalue lacking enable/output"
                              | not (hasEn && hasOut) ]
                          "value" ->
                              [ "method `" ++ m ++ "': value method with an enable"
                              | hasEn ] ++
                              [ "method `" ++ m ++ "': value method without an output"
                              | not hasOut ]
                          _ -> [] ]
    in  missing "method" expMeths actMeths ++
        extra "method" expMeths actMeths ++
        missing "clock" expClks actClks ++
        extra "clock" expClks actClks ++
        missing "reset" expRsts actRsts ++
        extra "reset" expRsts actRsts ++
        missing "inout" expInos actInos ++
        extra "inout" expInos actInos ++
        shapeErrs
