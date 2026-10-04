-- | The invocation's adapter from the unchanged .ba format to compiler input.
module LegacyArtifactReader(readLegacyArtifact) where

import Warmup ()
-- Order the executable's legacy adapters: GHC 9.14 links --make home objects
-- in compilation-completion order, even with -fobject-determinism.
import LegacyOptionsDriver ()
import ABinUtil(ArtifactReader)
import LegacyBA(legacyABin)
import LegacyBARead(readLegacyBAFile)

readLegacyArtifact :: ArtifactReader
readLegacyArtifact errh filename bytes =
    let (envelope, hash) = readLegacyBAFile errh filename bytes
    in return (legacyABin envelope, hash)
