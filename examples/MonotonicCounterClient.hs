module MonotonicCounterClient where

import RG
import MonotonicCounter
import LockfreeMonotonicCounter
import Control.Exception -- assert

{-@ client :: ((RGRef<{\x -> x > 0}, {\x y -> x <= y}, {\x y -> x <= y}> Int) -> IO ()) -> IO () @-}
client ::  (RGRef Int -> IO ()) -> IO ()
client other = do { r <- alloc_counter ();
                    atomic_inc r;
                    v1 <- readRGRef r;
                    other r;
                    v2 <- readRGRef r;
                    return (assert (v1 <= v2) ())
                  }
