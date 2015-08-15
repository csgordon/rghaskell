module MonotonicCounter where

import RG

-- Monotonically increasing counter!
{-@ alloc_counter :: () -> IO (RGRef<{\x -> x > 0}, {\x y -> x <= y}, {\x y -> x <= y}> Int) @-}
alloc_counter :: () -> IO (RGRef Int)
alloc_counter _ = newRGRef 1

{-@ inc_counter :: RGRef<{\x -> x > 0}, {\x y -> x <= y}, {\x y -> x <= y}> Int -> IO () @-}
inc_counter :: RGRef Int -> IO ()
inc_counter r = modifyRGRef r (\x -> x + 1)

-- Once we get bindIO working, give the bindIO and IO refinements a workout
{- inc_counter2 :: r:RGRef<{\x -> x > 0}, {\x y -> x <= y}, {\x y -> x <= y}> Int -> exists[x:Int].(IO<{\w -> (true)},{\w v -> (rgpointsTo r w x)}> ()) @-}
--inc_counter2 :: RGRef Int -> IO ()
--inc_counter2 r = readRGRef r 
--                 `bindIO` 
--                 storeOneMore r
--                 {-\v -> writeRGRef r v (v+1)-}

{-@ proves_nothing :: x:a -> y:a -> {v:a | (v = y)} @-}
proves_nothing :: a -> a -> a
proves_nothing x y = y --proves_nothing x y

main = do {
          r <- newRGRef 1; -- SHOULD BE ref{Int|>0}[<=,<=] (and is)
          r2 <- newRGRef 2;  -- SHOULD BE ref{Int|>0}[havoc,havoc].
          -- Instead we get the same as above....
          --r3 <- newRGRef 3 10 proves_reflexivity; -- BAD, correctly rejected
          c <- alloc_counter ();
          inc_counter r;
          inc_counter r2;
          inc_counter c;
          return ()
       }
