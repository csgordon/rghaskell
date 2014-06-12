module spec GHC.Base.IO where

--measure pointsTo :: IORef a -> RealWorld -> a -> {v:Bool | (Prop v)}


data GHC.Base.IO a <p :: RealWorld -> Prop , q :: RealWorld -> a -> Prop >
     = IO (act :: (RealWorld<p> -> ( RealWorld , a )<q>)) -- Should be (# RealWorld, a #)

-- assume GHC.Base.IO.bindIO :: forall <p :: RealWorld -> Prop, q :: RealWorld -> a -> Prop, r :: a -> RealWorld -> a -> Prop>.
                          --(IO<p,q> a -> (x:a -> IO<q x,r x>) -> IO<p,{\ w v -> exists[x:a]. r x w v}> b)

--assume readIORef :: x:{v: IORef a | true } -> {io:IO a <{\x -> True}, pointsTo x> | true})
