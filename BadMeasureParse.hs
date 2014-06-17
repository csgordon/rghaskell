module BadMeasureParse where

{-@ measure multiParam :: Int -> Int -> Prop @-}

{-@ assume v :: {x : Int | (multiParam x (x+1))} @-}
v :: Int
v = undefined
