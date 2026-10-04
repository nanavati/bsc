-- | Driver-owned convenience interface to this build's compiler identity.
-- Libraries receive CompilerVersion explicitly instead of importing this module.
module Version(bluespec, bscVersionStr, versionStr, versionname,
               copyright, buildnum, compilerVersion
              ) where

import Warmup ()
import BuildVersion(buildVersion, buildVersionNum, buildVersionName)
import CompilerVersion

compilerVersion :: CompilerVersion
compilerVersion = CompilerVersion
    { compilerVersionName = buildVersionName
    , compilerBuildVersion = buildVersion
    , compilerBuildNumber = buildVersionNum
    }

{-# NOINLINE versionname #-}
versionname :: String
versionname = compilerVersionName compilerVersion

buildnum :: Integer
buildnum = compilerBuildNumber compilerVersion

versionStr :: Bool -> String -> String
versionStr = formatVersion compilerVersion

bscVersionStr :: Bool -> String
bscVersionStr = formatBscVersion compilerVersion
