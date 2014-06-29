module RG where

import Language.Haskell.Liquid.Prelude
import Data.IORef as R
import GHC.Base

{- This is the main implementation of rgref primitives -}

{- We wrap IORefs in a new constructor to add ghost parameters for the predicate and
   relation(s).  It is a standard GHC optimization to eliminate the overhead since there is a single
   constructor with one physical argument, so at runtime these will look the same as IORefs:
   we won't pay time or space overhead. (In fact, in GHC, IORefs are a single constructor wrapping an STRef.) -}
{-@ data RGRef a <p :: a -> Prop, r :: a -> a -> Prop > 
    = Wrap (rgref_ref :: R.IORef a<p>) @-}
data RGRef a = Wrap (R.IORef a)
    deriving Eq

-- !!!!!! Apparently this include directive is silently doing nothing
{-@ include <GHC/Base/IO.spec> @-}
{-@ measure pointsTo :: IORef a -> RealWorld -> a -> Prop @-}
{-@ qualif PointsTo(v:a, r:IORef a, w:RealWorld): (pointsTo r w v) @-}
{-@ data GHC.Base.IO a <p :: RealWorld -> Prop , q :: RealWorld -> a -> Prop >
     =  @-}
 -- was IO (io_act :: (RealWorld<p> -> ( RealWorld , a )<q>))
 -- Should be (# RealWorld, a #)
{- data Data.IORef.IORef a <p :: a -> Prop, r :: a -> a -> Prop > = -}

{-@ assume forgetIOTriple :: forall <p :: RealWorld -> Prop, r :: RealWorld -> a -> Prop>.
                             IO<p,r> a -> IO a @-}
forgetIOTriple :: IO a -> IO a
forgetIOTriple a = a

-- below, true should be {\w -> (q w x)} but this is a sort error, since explicit app of abstract
-- refinement isn't supported
{-
assume bindIO :: forall <p :: RealWorld -> Prop, q :: RealWorld -> a -> Prop, r :: a -> RealWorld -> b -> Prop>.
                          IO<p,q> a -> (x:a -> IO<{\w -> (true)},r x> b) -> (exists[x:a].(IO<p,r x> b))
-}
{-@ measure rgpointsTo :: RGRef a -> RealWorld -> a -> Prop @-}
{-@ qualif RGPointsTo(v:a, r:RGRef a, w:RealWorld): (rgpointsTo r w v) @-}
-- Encode rgpointsTo (Wrap r) (w) (v) = (pointsTo r w v)
{-@ axiom_rgpointsTo :: forall <p :: a -> Prop, r :: a -> a -> Prop>.
                        ref:IORef a ->
                        w:RealWorld ->
                        c:a ->
			{v:Bool | ((pointsTo ref w c) <=> (rgpointsTo (Wrap ref) w c))} 
@-}
axiom_rgpointsTo :: IORef a -> RealWorld -> a -> Bool
axiom_rgpointsTo = undefined

{- assume embed_pair_impl :: forall <p :: a -> b -> Prop, q :: c -> b -> Prop>.
                              (a,b)<p> ->
			      impl:(asP:(a,b)<p> -> {asQ:(a,c)<q> | (fst asQ = fst asP)}) ->
			      (a,c)<q>
-}

{-@ assume readIORefS :: x:{v: IORef a | true } -> IO<{\x -> (true)}, {\w v -> (pointsTo x w v)}> a @-}
readIORefS :: IORef a -> IO a
readIORefS = readIORef
{-# INLINE readIORefS #-}

{-@ assume writeIORef2 :: forall <p :: a -> Prop>. 
                          x:(IORef a<p>) -> 
                          old:a<p> -> 
                          new:a<p> -> 
                          (IO<{\w -> (pointsTo x w old)}, {\w v -> (pointsTo x w new)}> ()) @-}
writeIORef2 :: IORef a -> a -> a -> IO ()
writeIORef2 r old new = writeIORef r new
{-# INLINE writeIORef2 #-}

{- A stability proof can be embedded into LH as a function of type:
    x:a<p> -> y:a<r x> -> {v:a<p> | v = y}
    This encodes the requirement that knowing P x and R x y is sufficient to deduce P y.
-}

{- TODO: e2 is a hack to sidestep the inference of false for r,
   it forces r to be inhabited. -}
{-@ newRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    e:a<p> -> 
                    e2:a<r e> ->
                    f:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    IO (RGRef <p, r> a) @-}
newRGRef :: a -> a -> (a -> a -> a) -> IO (RGRef a)
newRGRef e e2 stabilityPf = do {
                            r <- newIORef e;
                            return (Wrap r)
                         }

-- It would be nice if I could tie this to readIORefS, but there's no place to use liquidAssume to
-- invoke the axiom_rgpointsto
{-@ assume readRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, pre :: RealWorld -> Prop>.
                    x:RGRef<p, r> a -> IO<pre, {\w v -> (rgpointsTo x w v)}> (a<p>) @-}
readRGRef (Wrap x) = readIORef x

-- Again, would be nice to tie to pointsTo
{-@ assume writeRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop>. 
                          x:(RGRef<p,r> a) -> 
                          old:a -> 
                          new:a<r old> -> 
                          (IO<{\w -> (rgpointsTo x w old)}, {\w v -> (rgpointsTo x w new)}> ()) @-}
writeRGRef :: RGRef a -> a -> a -> IO ()
writeRGRef  (Wrap x) old new = writeIORef x new

{- assume Data.IORef.modifyIORef :: forall <p :: a -> Prop>. IORef a<p> -> (a<p> -> a<p>) -> IO () @-}

{-@ modifyRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    rf:(RGRef<p, r> a) ->
                    f:(x:a<p> -> a<r x>) ->
                    pf:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    IO () @-}
modifyRGRef :: RGRef a -> (a -> a) -> (a -> a -> a) -> IO ()
modifyRGRef (Wrap x) f pf = modifyIORef x (\ v -> pf v (f v))

{-@ modifyRGRef' :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    RGRef<p, r> a ->
                    f:(x:a<p> -> a<r x>) ->
                    pf:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    IO () @-}
-- TODO: strictify, so we don't de-optimize modifyIORef' calls
modifyRGRef' :: RGRef a -> (a -> a) -> (a -> a -> a) -> IO ()
modifyRGRef' (Wrap x) f pf = modifyIORef' x (\ v -> pf v (f v))

{-@ atomicModifyRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    rf:(RGRef<p, r> a) ->
                    f:(x:a<p> -> a<r x>) ->
                    pf:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    IO () @-}
atomicModifyRGRef :: RGRef a -> (a -> a) -> (a -> a -> a) -> IO ()
atomicModifyRGRef (Wrap x) f pf = atomicModifyIORef' x (\ v -> (pf v (f v),()))

{- The following is an adaptation of atomCAS from GHC's testsuite/tests/concurrent/prog003/CASList.hs -}
{-@ rgCAS :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
             Eq a =>
             RGRef<p,r> a -> old:a<p> -> new:a<r old> ->
             pf:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
             IO Bool
@-}
rgCAS :: Eq a => RGRef a -> a -> a -> (a -> a -> a) -> IO Bool
rgCAS (Wrap ptr) old new pf =
   atomicModifyIORef' ptr (\ cur -> if cur == old
                                   then (pf old new, True)
                                   else (cur, False))
