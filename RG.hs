module RG where

import Data.IORef as R
import GHC.Base

{- Liquid Rely-Guarantee References / RG-Haskell

   This is an embedding of a slightly simplified rely-guarantee reference system.
   (See "Rely-Guarantee References for Refinement Types over Aliased Mutable Data,"
   by Gordon, Ernst, and Grossman, PLDI'13.  I promise to never use such a long paper
   title ever again.)

   The key idea in that paper is to augment each reference with a predicate refining
   the referent and heap reachable from it, and binary relations describing permitted
   local actions (the guarantee) and possible remote actions (the rely):
   
                ref{T|P}[R,G]
   
   The terminology comes from rely-guarantee reasoning, from the concurrent program
   logic literature.  As long as
   each reference's guarantee relation is a subrelation of any alias's rely (plus some
   subtle side conditions about nested references), any predicate P that is /stable/
   with respect to a rely R on a given reference (forall x y, P x -> R x y -> P y)
   is trivially preserved by any update through an alias that respects that alias's
   guarantee relation.

   Embedding into Liquid Haskell instead of Coq requires a few weakenings of the
   original design, so we lose expressiveness but gain substantially from automation
   and being a refinement of a language with real programs!  The main simplifications are:
    - TEMPORARILY, rely and guarantee are the same, until we get rolling.  In general,
      we must always have that the guarantee implies the rely, since Haskell wouldn't
      respect the substructural restrictions.  Leaving them the same makes weakening the
      guarantee unsound, so we should fix this soon.
    - Predicates and relations can refer only to the immediate referent for now.
    - Folding (pushing a local restriction through to new references reached via
      dereference) doesn't exist in this system, mostly because all predicates and
      relations can restrict only one cell.

-}


{- We wrap IORefs in a new constructor to add ghost parameters for the predicate and
   relation(s).  It is a standard GHC optimization to eliminate the overhead since there is a single
   constructor with one physical argument, so at runtime these will look the same as IORefs:
   we won't pay time or space overhead. (In fact, in GHC, IORefs are a single constructor wrapping an STRef.) -}
{-@ data RGRef a <p :: a -> Prop, r :: a -> a -> Prop > 
    = Wrap (rgref_ref :: R.IORef a<p>) @-}
data RGRef a = Wrap (R.IORef a)

-- !!!!!! Apparently this include directive is silently doing nothing
{-@ include <GHC/Base/IO.spec> @-}
{-@ measure pointsTo :: IORef a -> RealWorld -> a -> Prop @-}
{-@ data IO a <p :: RealWorld -> Prop , q :: RealWorld -> a -> Prop >
     =  @-}
 -- was IO (io_act :: (RealWorld<p> -> ( RealWorld , a )<q>))
 -- Should be (# RealWorld, a #)
{-@ data IORef a <p :: a -> Prop, r :: a -> a -> Prop > = @-}

-- below, true should be {\w -> (q w x)} but this is a sort error, since explicit app of abstract
-- refinement isn't supported
{-@
assume bindIO :: forall <p :: RealWorld -> Prop, q :: RealWorld -> a -> Prop, r :: a -> RealWorld -> b -> Prop>.
                          IO<p,q> a -> (x:a -> IO<{\w -> (true)},r x> b) -> (exists[x:a].(IO<p,r x> b))
@-}
{-@ 
measure rgpointsTo :: forall <p :: a -> Prop, r :: a -> a -> Prop>.
                          RGRef<p,r> a -> RealWorld -> a -> Prop
@-}
-- Encode rgpointsTo (Wrap r) (w) (v) = (pointsTo r w v)
{-@ axiom_rgpointsTo :: forall <p :: a -> Prop, r :: a -> a -> Prop>.
                        ref:RGRef<p,r> a ->
                        w:RealWorld ->
                        c:a ->
			{v:Bool | ((Prop v) <=> (pointsTo (rgref_ref ref) w c))} 
@-}
axiom_rgpointsTo :: RGRef a -> RealWorld -> a -> Bool
axiom_rgpointsTo = undefined

{-@ test_axiom :: forall <p :: a -> Prop, r :: a -> a -> Prop>.
    rr:RGRef<p,r> a ->
    ir:{i:IORef a | (rr = Wrap i)} -> -- For some reason, this refinement fails to parse...
    v:a ->
    w:{rw:RealWorld | (pointsTo ir rw v)} ->
    {w2:RealWorld | (rgpointsTo (Wrap ir) w2 v)}
@-}
test_axiom :: RGRef a -> IORef a -> a -> RealWorld -> RealWorld
test_axiom rr ir v w = w

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

-- Requires explicit type anno for LH type to refine the inferred Haskell type
{-@ stable_monocount :: x:{v:Int | v > 0 } -> y:{v:Int | x <= v } -> {v:Int | ((v = y) && (v > 0)) } @-}
stable_monocount :: Int -> Int -> Int
stable_monocount x y = y

-- Testing / debugging function
{-@ generic_accept_stable :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    f:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    ()
                    @-}
generic_accept_stable :: (a -> a -> a) -> ()
generic_accept_stable pf = ()

{-@ proves_reflexivity :: x:{v:Int | v > 0} -> y:{v:Int | v > 0} -> {v:Int | v > 0} @-}
proves_reflexivity :: Int -> Int -> Int
proves_reflexivity x y = x

test :: ()
test = generic_accept_stable proves_reflexivity

{-@ proves_nothing :: x:a -> y:a -> {v:a | (v = y)} @-}
proves_nothing :: a -> a -> a
proves_nothing x y = y --proves_nothing x y

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

{- blah :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
            x:IORef a ->
            IO<{\x -> (true)}, {\w v -> (pointsTo x w v)}> a ->
            IO<{\x -> (true)}, {\w v -> (rgpointsTo (Wrap x) w v)}> a
            @-}
--blah :: IORef a -> IO a -> IO a
--blah r io = io

-- It would be nice if I could tie this to readIORefS, but there's no place to use liquidAssume to
-- invoke the axiom_rgpointsto
{-@ assume readRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    x:RGRef<p, r> a -> IO<{\x -> (true)}, {\w v -> (rgpointsTo x w v)}> (a<p>) @-}
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

-- An anonymous fn inside modifyRGref doesn't work after updating
-- (modifyIORef's type loses the refinements)
{-@ coerce :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
              f:(x:a<p> -> a<r x>) ->
              pf:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
	      a<p> ->
	      a<p> @-}
coerce :: (a -> a) -> (a -> a -> a) -> a -> a
coerce f pf v = pf v (f v)

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




-- Monotonically increasing counter!
{-@ alloc_counter :: () -> IO (RGRef<{\x -> x > 0}, {\x y -> x <= y}> Int) @-}
alloc_counter :: () -> IO (RGRef Int)
alloc_counter _ = newRGRef 1 3 stable_monocount

{-@ inc_counter :: RGRef<{\x -> x > 0}, {\x y -> x <= y}> Int -> IO () @-}
inc_counter :: RGRef Int -> IO ()
inc_counter r = modifyRGRef r (\x -> x + 1) stable_monocount

-- Now give the bindIO and IO refinements a workout
{-@ inc_counter2 :: r:RGRef<{\x -> x > 0}, {\x y -> x <= y}> Int -> exists[x:Int].(IO<{\w -> (true)},{\w v -> (rgpointsTo r w x)}> ()) @-}
inc_counter2 :: RGRef Int -> IO ()
inc_counter2 r = do {
                       readRGRef r `bindIO` \v ->
                       writeRGRef r v (v+1)
                    }

main = do {
          r <- newRGRef 1 3 stable_monocount; -- SHOULD BE ref{Int|>0}[<=,<=] (and is)
          r2 <- newRGRef 2 9 proves_nothing;  -- SHOULD BE ref{Int|>0}[havoc,havoc].
          -- Instead we get the same as above....
          --r3 <- newRGRef 3 10 proves_reflexivity; -- BAD, correctly rejected
          c <- alloc_counter ();
          return ()
       }


-- The LH folks fixed this
---- What are the subtyping rules for data structure params that aren't
---- used within the structure?
--{- unused_contra :: RGRef <{\x -> x > 0}, {\x y -> x <= y}> Int -> RGRef <{\x -> x > 0}, {\x y -> false}> Int @-}
--unused_contra :: RGRef Int -> RGRef Int
--unused_contra r = r
--
--
--{- unused_covar :: RGRef <{\x -> x > 0}, {\x y -> false}> Int -> RGRef <{\x -> x > 0}, {\x y -> x <= y}> Int @-}
--unused_covar :: RGRef Int -> RGRef Int
--unused_covar r = r
---- It looks like there's simply no constraint!
--
