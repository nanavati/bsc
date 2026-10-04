{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ >= 914
{-# OPTIONS_GHC -fobject-determinism #-}
#endif
module SetupHooks (setupHooks) where
import BscSetupHooks (bscSetupHooks)
import Distribution.Simple.SetupHooks (SetupHooks)
setupHooks :: SetupHooks
setupHooks = bscSetupHooks
