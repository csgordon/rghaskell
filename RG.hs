module RG where

import Language.Haskell.Liquid.Prelude
import Data.IORef as R
import GHC.Base

{- This is the main implementation of rgref primitives -}

{- We wrap IORefs in a new constructor to add ghost parameters for the predicate and
   relation(s).  It is a standard GHC optimization to eliminate the overhead since there is a single
   constructor with one physical argument, so at runtime these will look the same as IORefs:
   we won't pay time or space overhead. (In fact, in GHC, IORefs are a single constructor wrapping an STRef.) -}
{-@ data RGRef a <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop > 
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

{-@ assume forgetIOTriple :: forall <p :: RealWorld -> Prop, r :: RealWorld -> a -> Prop, q :: a -> Prop>.
                             IO<p,r> (a<q>) -> IO (a<q>) @-}
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
{- A relational implication can be embedded as a function of type:
    x:a -> y:a<g x> -> {v:() | r x y }
-}

{-@ measure getfst :: (a, b) -> a
    getfst (x, y) = x
  @-}
{-@ measure getsnd :: (a, b) -> b
    getsnd (x, y) = y
  @-}

{- TODO: e2 is a hack to sidestep the inference of false for r,
   it forces r to be inhabited. -}
-- ((r (getfst v) (getsnd v)) /\ (v = (x,y)))
{-@ newRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
                    {x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}}
                    {x:a<p> -> y:a<g x> -> {v:a<r x> | (v = y) }}
                    e:a<p> -> 
                    e2:a<g e> ->
                    IO (RGRef <p, r, g> a) @-}
newRGRef :: a -> a -> IO (RGRef a)
newRGRef e e2 = do {
                            r <- newIORef e;
                            return (Wrap r)
                         }

-- We'll be needing some witness of past values
{-@ measure pastValue :: RGRef a -> a -> Prop @-}
{-@ qualif PastValue(r:RGRef a, x:a): (pastValue r x) @-}
{-@ measure terminalValue :: RGRef a -> a @-}
{-@ qualif TerminalValue(r:RGRef a): (terminalValue r) @-}

{-@ assume axiom_pastIsTerminal :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>.
                             {x:{x:a | x = v} -> y:a<r x> -> {z:a | ((z = y) && (z = x))}}
                             {x:{x:a | x = v} -> y:a<g x> -> {z:a | ((z = y) && (z = x))}}
                             ref:RGRef<p,r,g> a ->
                             v:{v:a | (pastValue ref v)} ->
                             { b : Bool | (((terminalValue ref) = v) <=> (pastValue ref v))}
                             @-}
axiom_pastIsTerminal :: RGRef a -> a -> Bool
axiom_pastIsTerminal = undefined

{-@ assume typecheck_pastval :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>.
                                x:RGRef<p,r,g> a ->
                                v:{v:a | (pastValue x v)} ->
                                {q:a | (q = v)} @-}
typecheck_pastval :: RGRef a -> a -> a
typecheck_pastval x v = v

-- It would be nice if I could tie this to readIORefS, but there's no place to use liquidAssume to
-- invoke the axiom_rgpointsto
{-@ assume readRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop, pre :: RealWorld -> Prop>.
                    x:RGRef<p, r, g> a -> IO<pre, {\w v -> (rgpointsTo x w v)}> ({res:a<p> | (pastValue x res)}) @-}
readRGRef (Wrap x) = readIORef x

{-@ assume readRGRef2 :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop, pre :: RealWorld -> Prop>.
                    x:RGRef<p, r, g> a -> IO ({res:a<p> | (pastValue x res)}) @-}
readRGRef2 (Wrap x) = readIORef x

-- Again, would be nice to tie to pointsTo
{-@ assume writeRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>. 
                          x:(RGRef<p,r,g> a) -> 
                          old:a -> 
                          new:a<r old> -> 
                          (IO<{\w -> (rgpointsTo x w old)}, {\w v -> (rgpointsTo x w new)}> ()) @-}
writeRGRef :: RGRef a -> a -> a -> IO ()
writeRGRef  (Wrap x) old new = writeIORef x new

{- assume Data.IORef.modifyIORef :: forall <p :: a -> Prop>. IORef a<p> -> (a<p> -> a<p>) -> IO () @-}

{-@ modifyRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
                    {x:a<p> -> y:a<g x> -> {v:a<p> | (v = y)}}
                    rf:(RGRef<p, r, g> a) ->
                    f:(x:a<p> -> a<g x>) ->
                    IO () @-}
modifyRGRef :: RGRef a -> (a -> a) -> IO ()
modifyRGRef (Wrap x) f = modifyIORef x f --(\ v -> pf v (f v))

{-@ modifyRGRef' :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
                    {x:a<p> -> y:a<g x> -> {v:a<p> | (v = y)}}
                    rf:(RGRef<p, r, g> a) ->
                    f:(x:a<p> -> a<g x>) ->
                    IO () @-}
-- TODO: strictify, so we don't de-optimize modifyIORef' calls
modifyRGRef' :: RGRef a -> (a -> a) -> IO ()
modifyRGRef' (Wrap x) f = modifyIORef' x f --(\ v -> pf v (f v))

{-@ atomicModifyRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
                    {x:a<p> -> y:a<g x> -> {v:a<p> | (v = y)}}
                    rf:(RGRef<p, r, g> a) ->
                    f:(x:a<p> -> a<g x>) ->
                    IO () @-}
atomicModifyRGRef :: RGRef a -> (a -> a) -> IO ()
atomicModifyRGRef (Wrap x) f = atomicModifyIORef' x (\ v -> ((f v),()))

{- The following is an adaptation of atomCAS from GHC's testsuite/tests/concurrent/prog003/CASList.hs -}
{-@ rgCAS :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
             {x:a<p> -> y:a<g x> -> {v:a<p> | (v = y)}}
             Eq a =>
             RGRef<p,r,g> a -> old:a<p> -> new:a<g old> ->
             IO Bool
@-}
rgCAS :: Eq a => RGRef a -> a -> a -> IO Bool
rgCAS (Wrap ptr) old new =
   atomicModifyIORef' ptr (\ cur -> if cur == old
                                   then (new, True)
                                   else (cur, False))
