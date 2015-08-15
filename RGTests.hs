module RGTests where

import RG
import Data.IORef
import GHC.Base
import Language.Haskell.Liquid.Prelude

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


{-@ coerce :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
              f:(x:a<p> -> a<r x>) ->
              pf:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
	      a<p> ->
	      a<p> @-}
coerce :: (a -> a) -> (a -> a -> a) -> a -> a
coerce f pf v = pf v (f v)

{-@ test_injectStable :: r:RGRef<{\x -> x > 0},{\x y -> x <= y},{\x y -> x <= y}> Int ->
                         {v : Int | ((pastValue r v) && (v > 20))} ->
                         {x : RGRef<{\x -> x > 20},{\x y -> x <= y},{\x y -> x <= y}> Int | x = r} @-}
test_injectStable :: RGRef Int -> Int -> RGRef Int
test_injectStable r v = injectStable r v









