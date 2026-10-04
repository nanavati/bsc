-- | In-memory elaboration output, independent of scheduling and backends.
-- Existing artifacts retain their baseline serialization.
module AModule (AModuleInfo(..), AModule(..)) where

import Warmup ()
import ASyntax (APackage)
import CType (CQType)
import Id (Id)
import Pragma (PProp)

-- | Source identity and declarations shared by both phases, including options
-- declared in the source. Invocation flags and execution state remain inputs
-- to each phase rather than artifact data.
data AModuleInfo = AModuleInfo
    { ami_name :: Id
    , ami_original_type :: CQType
    , ami_pragmas :: [PProp]
    , ami_is_function :: Bool
    , ami_source_prefix :: String
    , ami_source_package :: String
    }

-- | Elaborated and cleaned ASyntax passed to scheduling.
data AModule = AModule
    { amod_info :: AModuleInfo
    , amod_body :: APackage
    }
