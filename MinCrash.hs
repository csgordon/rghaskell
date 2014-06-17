module MinCrash where

import Data.IORef

{-@ data IRef a <p :: a -> Prop> 
    = Wrap (iref_ref :: IORef a<p>) @-}
data IRef a = Wrap (IORef a)

-- With this STM refinement, the compiler crashes.  Without it, everything is fine.
-- In fact, simply removing the explicit specification of the parameter to IRef allows the
-- compiler to finish.
{-@ data STM a = STM (stm_log_ref :: (IRef<{\ x -> true}> (IO ()) -> IO a)) @-}
data STM a = STM (IRef (IO ()) -> IO a)

unSTM :: STM a -> IRef (IO ()) -> IO a
unSTM (STM f) = f
