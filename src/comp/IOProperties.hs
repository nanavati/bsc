-- Port-property view shared by semantic analysis and legacy Verilog comments.
-- VModInfo is deliberately unchanged; the phase boundary reuses its properties.
module IOProperties
    ( VIOProps(..), IOIO(..), ioPropertiesPorts, joinOutProps, joinInProps, size ) where

import Warmup ()
import Data.List(intersect)
import Eval(NFData(..), rnf)
import Util(itos)
import PPrint
import ErrorUtil(internalError)
import Id(getIdString)
import PreIds(idPrimAction, idInout_, idPrimUnit)
import VModInfo(VeriPortProp(..), VName(..), VPort)
import ASyntax(AId, AType(..))

data IOIO = INPUT | OUTPUT | INOUT deriving (Eq)

instance NFData IOIO where rnf x = seq x ()

--   (name, direction, width, properties)
newtype VIOProps = VIOProps [(AId, IOIO, Integer, [VeriPortProp])]
        deriving (Eq)

-- The field names of the existing interface schema are shared by backends;
-- this view only projects saved facts and performs no port analysis.
ioPropertiesPorts :: VIOProps -> [VPort]
ioPropertiesPorts (VIOProps ports) =
    [(VName (getIdString name), props) | (name, _, _, props) <- ports]

instance NFData VIOProps where
    rnf (VIOProps xs) = rnf xs

instance PPrint VIOProps where
    pPrint d p (VIOProps ps) =
                text "Name                         I/O  size props" $+$
                foldr ($+$) (text "") (map pp ps)
        where pp (i, io, sz, ps) =
                let s = getIdString i
                    si = s ++ replicate (29 - length s) ' '
                    n = itos sz
                    sn = replicate (5 - length n) ' ' ++ n
                    iotxt = case (io) of
                              INPUT -> " I"
                              OUTPUT-> " O"
                              INOUT -> "IO"
                in  text si <+> text iotxt <+>
                    text sn <+> sep (map (pPrint d 0) ps)

-- given the props for multiple signals,
-- compute the props that the concatenation should have
joinOutProps :: [[VeriPortProp]] -> [VeriPortProp]
joinOutProps (x:xs) = foldr intersect x xs
-- empty list only occurs with prims of no args
-- XXX do we have any? if they all give constant return values,
-- XXX then we could return [VPconst] here
joinOutProps [] = []

-- given the deduced props for multiple signals,
-- compute the props that should be deduced for a signal
-- which connects directly to all these signals (and only these)
joinInProps :: [[VeriPortProp]] -> [VeriPortProp]
joinInProps pss =
    let
        -- if a signal is unused, it might as well not exist,
        -- so don't count it
        pss' = filter (VPunused `notElem`) pss
    in
        case pss' of
            [] -> [VPunused]
            (x:xs) ->
                -- otherwise, a prop needs to be on all used signals
                -- for it to be on the source
                foldr intersect x xs


-- compute the size of a port
size :: AType -> Integer
size (ATBit n) = n
size (ATAbstract a _) | a == idPrimAction = 1
size (ATAbstract a [n]) | a == idInout_ = n
size (ATAbstract a _) | a == idPrimUnit = 0
size (ATString _ ) = 0
size t = internalError ("getIOProps.size: " ++ show t)
