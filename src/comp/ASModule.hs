-- | In-memory scheduled-module boundary. This type is not serialized;
-- existing .ba files retain their baseline layout through the legacy codec.
module ASModule (ASModule(..)) where

import Warmup ()
import AModule (AModuleInfo)
import ADumpScheduleInfo (MethodDumpInfo)
import AScheduleInfo (AScheduleInfo)
import ASyntax (APackage)
import VModInfo (VSchedInfo, VPathInfo)

-- | Scheduling output passed back to the driver. Existing preparation and
-- serialization retain their original order and consume these explicit values.
data ASModule = ASModule
    { smod_info :: AModuleInfo
    , smod_body :: APackage
    , smod_schedule :: AScheduleInfo
    , smod_wrapper_schedule :: VSchedInfo
    , smod_method_dump :: MethodDumpInfo
    , smod_path_info :: VPathInfo
    }
