module Problems where

import Control.Monad
import Data.IORef
import Control.Concurrent
import Control.Concurrent.Chan
import System.Environment
import Data.Time

import RG
import Language.Haskell.Liquid.Prelude



{-@ predicate SetRG X Y =
    (((IsNull X) && (IsNode Y)) ||
     ((IsNode X) && (IsDel Y) && ((val X) = (val Y)) && ((nxt X) = (nxt Y))) ||
     ((IsNode X) && (IsNode Y) && (IsDel (terminalValue (nxt X))) && ((val X) = (val Y)) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     ((IsHead X) && (IsHead Y) && (IsDel (terminalValue (nxt X))) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     ((IsNode X) && (IsNode Y) && ((val X) = (val Y)) && (nxt X = nxt (shareValue (nxt Y)))) ||
     ((IsHead X) && (IsHead Y) && (nxt X = nxt (shareValue (nxt Y)))) ||
     (X = Y)
     )
@-}
{-@
data Set a <p :: a -> Prop > = 
    Node (node_val :: a<p>) (slack :: { v : a | node_val <= v}) (node_next :: ((RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a))))
  | DelNode (del_val :: a<p>) (slack :: { v : a | del_val <= v}) (del_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a)))
  | Null
  | Head (head_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (1 > 0)}> a)))
@-}
data Set a = Node a a ((RGRef (Set a)))
            | DelNode a a ((RGRef (Set a)))
            | Null
            | Head ((RGRef (Set a))) deriving Eq


-- ISSUE 1: crash when checking myNext
{-@ myNext :: l:{x:Set a | not (IsNull x) } -> 
              {r:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> ((IsHead l) || (slack l < x))}> a) |
                   ((nxt l) = r) }
@-}
myNext :: Set a -> RGRef (Set a)
myNext (Node v lb n) = n
myNext (DelNode v lb n) = n
myNext (Head n) = n

{-@ measure nodeclass :: Set a -> Int
    nodeclass (Head n) = 0
    nodeclass (Node v lb n) = 1
    nodeclass (DelNode v lb n) = 2
    nodeclass (Null) = 3
    @-}
{-@ predicate IsHead X = (nodeclass X = 0) @-}
{-@ predicate IsNode X = (nodeclass X = 1) @-}
{-@ predicate IsDel X  = (nodeclass X = 2) @-}
{-@ predicate IsNull X = (nodeclass X = 3) @-}
{-@ measure nxt :: Set a -> (RGRef (Set a))
    nxt (Node v lb n) = n
    nxt (DelNode v lb n) = n
    nxt (Head n) = n
@-}
{-@ measure val :: Set a -> a
    val (Node v lb n) = v
    val (DelNode v lb n) = v
@-}

-- ISSUE 2: Can't instantiate an axiom properly
-- When this is Int, it works.  When we use Set Int, it fails, giving a message that includes the
-- body of SetRG even though it's not explicitly here... something's up with the recursive pointer
{-@ injectStable3 :: forall <p :: (Set Int) -> Prop, 
                                         q :: (Set Int) -> Prop,
                                         r :: (Set Int) -> (Set Int) -> Prop,
                                         g :: (Set Int) -> (Set Int) -> Prop,
                                         z :: Int -> Prop>.
                    {x::(Set <z> Int)<q> |- (Set <z> Int)<r x> <: (Set <z> Int)<q>}
                    ref:RGRef<p,r,g> (Set <z> Int) ->
                    {v:(Set <z> Int)<q> | (pastValue ref v)} ->
                    {r : (RGRef<q,r,g> (Set <z> Int)) | (ref = r)} @-}
injectStable3 :: RGRef (Set Int) -> (Set Int) -> RGRef (Set Int)
injectStable3 ref v = injectStable ref v

-- trying without <z>
{-@ injectStable4 :: forall <p :: (Set Int) -> Prop, 
                                         q :: (Set Int) -> Prop,
                                         r :: (Set Int) -> (Set Int) -> Prop,
                                         g :: (Set Int) -> (Set Int) -> Prop>.
                    {x::(Set Int)<q> |- (Set Int)<r x> <: (Set Int)<q>}
                    ref:RGRef<p,r,g> (Set Int) ->
                    {v:(Set Int)<q> | (pastValue ref v)} ->
                    {r : (RGRef<q,r,g> (Set Int)) | (ref = r)} @-}
injectStable4 :: RGRef (Set Int) -> (Set Int) -> RGRef (Set Int)
injectStable4 ref v = injectStable ref v


{-@ injectExplicit :: forall <p :: (Set Int) -> Prop, 
                                         q :: (Set Int) -> Prop,
                                         r :: (Set Int) -> (Set Int) -> Prop,
                                         g :: (Set Int) -> (Set Int) -> Prop>.
                    pf:(j:(Set Int)<q> -> k:(Set Int)<r j> -> {z:(Set Int)<q> | z = k}) ->
                    ref:RGRef<p,r,g> (Set Int) ->
                    {v:(Set Int)<q> | (pastValue ref v)} ->
                    {r : (RGRef<q,r,g> (Set Int)) | (ref = r)} @-}
injectExplicit :: ((Set Int) -> (Set Int) -> (Set Int)) -> RGRef (Set Int) -> (Set Int) -> RGRef (Set Int)
injectExplicit pf ref v = injectStable2 pf ref v

{-@ assume isDelOnly :: x:Set a -> 
                        {v:Bool | ((IsDel x) <=> ((not (IsHead x)) && (not (IsNull x)) && (not (IsNode x))))} @-}
isDelOnly :: Set a -> Bool
isDelOnly x = True
{-@ assume isNodeOnly :: x:Set a -> 
                        {v:Bool | ((IsNode x) <=> ((not (IsHead x)) && (not (IsNull x)) && (not (IsDel x))))} @-}
isNodeOnly :: Set a -> Bool
isNodeOnly x = True
{-@ injectBound :: forall <z :: a -> Prop, s :: Set a -> Prop>.
             { x::a |- (Set<z> a)<s> <: {v:Set<z> a | (IsNode v || IsDel v) && val v < x } }
             {x::(Set<z> a)<s> |- (Set<z> a)<SetRG x> <: (Set<z> a)<s>}
             ref:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <z> a) ->
             x:a ->
             {n:(Set<z> a)<s> | pastValue ref n} ->
             {r:RGRef<s,{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <z> a) | r = ref } @-}
injectBound :: RGRef (Set a) -> a -> Set a -> RGRef (Set a)
injectBound ref x n = injectStable ref (liquidAssume (isDelOnly n) (liquidAssume (isNodeOnly n) n))
