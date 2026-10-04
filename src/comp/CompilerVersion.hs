-- | Explicit compiler identity supplied by the driver. This module contains
-- no build-generated values or Git lookup. A phase result key must include
-- the fields it consumes in source semantics, emitted metadata or compatibility
-- decisions (including predefined version macros and language constants);
-- library implementation fingerprints are independent of this value.
module CompilerVersion
    ( CompilerVersion(..)
    , bluespec, copyright
    , formatVersion, formatBscVersion
    ) where

import Warmup ()

data CompilerVersion = CompilerVersion
    { compilerVersionName :: String
    , compilerBuildVersion :: String
    , compilerBuildNumber :: Integer
    } deriving (Eq, Show)

{-# NOINLINE bluespec #-}
{-# NOINLINE copyright #-}

bluespec :: String
bluespec = "Bluespec"

-- | The historical version-string format, with identity passed explicitly.
formatVersion :: CompilerVersion -> Bool -> String -> String
formatVersion identity showVersion toolname
  | not showVersion = toolname
  | otherwise =
    let emptyOr a b = if null a then a else b
        versionname = compilerVersionName identity
        buildVersion = compilerBuildVersion identity
        versionstr  = versionname `emptyOr` (", version " ++ versionname)
        buildstr    = buildVersion `emptyOr` (" (build " ++ buildVersion ++ ")")
    in concat [toolname, versionstr, buildstr]

formatBscVersion :: CompilerVersion -> Bool -> String
formatBscVersion identity showVersion =
    formatVersion identity showVersion (bluespec ++ " Compiler")

copyright :: String
copyright = unlines copyrights

copyrights :: [String]
copyrights = ["This is free software; for source code and copying conditions, see",
              "https://github.com/B-Lang-org/bsc"]
