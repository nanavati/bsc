-- Foreign-function serialization moved verbatim from baseline GenABin.
-- This module introduces no new artifact format or metadata fields.
module BinForeignFunctions () where

import Warmup ()
import BinData
import ErrorUtil(internalError)
import ForeignFunctions(ForeignType(..), ForeignFunction(..))

instance Bin ForeignType where
    writeBytes Void        = do putI 0
    writeBytes (Narrow n)  = do putI 1; toBin n
    writeBytes (Wide n)    = do putI 2; toBin n
    writeBytes Polymorphic = do putI 3
    writeBytes StringPtr   = do putI 4
    readBytes = do i <- getI
                   case i of
                     0 -> return Void
                     1 -> do n <- fromBin; return (Narrow n)
                     2 -> do n <- fromBin; return (Wide n)
                     3 -> return Polymorphic
                     4 -> return StringPtr
                     n -> internalError $ "GenABin.Bin(ForeignType).readBytes: " ++ show n

instance Bin ForeignFunction where
    writeBytes (FF name rt args) = do toBin name; toBin rt; toBin args
    readBytes = do name <- fromBin
                   rt   <- fromBin
                   args <- fromBin
                   return (FF name rt args)
