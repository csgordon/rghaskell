module spec GHC.Base where

assume bindIO :: forall <p :: RealWorld -> Prop, q :: RealWorld -> a -> Prop, r :: a -> RealWorld -> a -> Prop>.
                          (IO<p,q> a -> (x:a -> IO<q x,r x>) -> IO<p,{\ w v -> (exists[x:a].(r x w v))}> b)
