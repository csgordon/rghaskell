module LockfreeMonotonicCounter where

import RG
import MonotonicCounter

{-@ atomic_inc :: RGRef<{\x -> x > 0}, {\x y -> x <= y}, {\x y -> x <= y}> Int -> IO () @-}
atomic_inc :: RGRef Int -> IO ()
atomic_inc r = atomicModifyRGRef r (\x -> x + 1) stable_monocount
