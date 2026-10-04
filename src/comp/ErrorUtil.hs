-- | Internal failures carry diagnostic data without depending on invocation
-- metadata. Executable drivers attach their compiler version when reporting.
module ErrorUtil (internalError, InternalCompilerError(..)) where

import Warmup ()
import qualified Control.Exception as CE

newtype InternalCompilerError = InternalCompilerError String
    deriving (Show)

instance CE.Exception InternalCompilerError

{-# NOINLINE internalError #-}
-- This is called from anywhere, even when not in the IO monad. Keep a distinct
-- exception type so user-error recovery never mistakes an internal failure for
-- an ErrorCall and continues compilation with a poisoned definition.
internalError :: String -> a
internalError = CE.throw . InternalCompilerError
