-- | Resolved module inputs for backend generation. Artifact discovery and
-- decoding belong to the driver; backends consume this format-neutral view.
module ArtifactHierarchy
    ( HierMap, InstModMap, ABinMap, ResolvedHierarchy(..) ) where

import Warmup ()
import qualified Data.Map as M
import ABin(ABinModInfo)
import ForeignFunctions(ForeignFuncMap)
import Id(Id)

-- | Module name to ordinary and no-inline submodule instances.
type HierMap = M.Map String ([(String, String)], [(String, String)])

-- | Hierarchical instance name to module name; the root instance is "".
type InstModMap = M.Map String String

-- | Module name to its source artifact, retained for generated-file reuse.
type ABinMap = M.Map String FilePath

-- | A hierarchy whose modules have been loaded, checked for scheduling
-- errors and prepared for the selected backend. Consumers receive the same
-- module bodies as the existing loader, without depending on its codec.
-- The compiler version accompanies each module body.
data ResolvedHierarchy = ResolvedHierarchy
    { hierarchyTopModule :: Id
    , hierarchyModules :: HierMap
    , hierarchyInstances :: InstModMap
    , hierarchyForeignFunctions :: ForeignFuncMap
    , hierarchyArtifactFiles :: ABinMap
    , hierarchyModuleInfos :: [(String, (ABinModInfo, String))]
    }
