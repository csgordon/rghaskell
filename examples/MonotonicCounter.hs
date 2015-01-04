module MonotonicCounter where

import RG

-- Requires explicit type anno for LH type to refine the inferred Haskell type
{-@ stable_monocount :: x:{v:Int | v > 0 } -> y:{v:Int | x <= v } -> {v:Int | ((v = y) && (v > 0)) } @-}
stable_monocount :: Int -> Int -> Int
stable_monocount x y = y

{-@ le_refl :: x:Int -> y:{v:Int | x <= v } -> {v:Int | ((x <= v) && (v = y)) } @-}
le_refl :: Int -> Int -> Int
le_refl x y = y

-- Monotonically increasing counter!
{-@ alloc_counter :: () -> IO (RGRef<{\x -> x > 0}, {\x y -> x <= y}, {\x y -> x <= y}> Int) @-}
alloc_counter :: () -> IO (RGRef Int)
alloc_counter _ = newRGRef 1 3 stable_monocount le_refl

{-@ inc_counter :: RGRef<{\x -> x > 0}, {\x y -> x <= y}, {\x y -> x <= y}> Int -> IO () @-}
inc_counter :: RGRef Int -> IO ()
inc_counter r = modifyRGRef r (\x -> x + 1) stable_monocount

{-@ storeOneMore :: r:RGRef<{\x -> x > 0}, {\x y -> x <= y}, {\x y -> x <= y}> Int ->
                    v:Int ->
                    (exists[v2:Int].
                    (IO<{\w -> (rgpointsTo r w v)}, {\w q -> ((v2 = v + 1) && (rgpointsTo r w v2))}> ())) @-}
                    -- Changing second refinement to rgpointsTo r w (v+1) as it should be gives a
                    -- parse error
storeOneMore :: RGRef Int -> Int -> IO ()
storeOneMore r v = writeRGRef r v (v+1)

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
          r <- newRGRef 1 3 stable_monocount le_refl; -- SHOULD BE ref{Int|>0}[<=,<=] (and is)
          r2 <- newRGRef 2 9 proves_nothing le_refl;  -- SHOULD BE ref{Int|>0}[havoc,havoc].
          -- Instead we get the same as above....
          --r3 <- newRGRef 3 10 proves_reflexivity; -- BAD, correctly rejected
          c <- alloc_counter ();
          return ()
       }
