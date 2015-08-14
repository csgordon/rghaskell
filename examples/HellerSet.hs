{-# LANGUAGE BangPatterns,CPP #-}
-- Disable termination checking; this is lock-free, not wait-free
{-@ LIQUID "--no-termination" @-}
module HellerSet where

import Control.Monad
import Data.IORef
import Control.Concurrent
import Control.Concurrent.Chan
import System.Environment
import Data.Time

import RG
import Language.Haskell.Liquid.Prelude

-- #define USE_UNPACK
-- #define USE_STRICT

#if defined(USE_UNPACK)
#define UNPACK(p) {-# UNPACK #-} !(p)
#elif defined(USE_STRICT)
#define UNPACK(p) !(p)
#else
#define UNPACK(p) p
#endif


-- Rely/Guarantee for next-pointers:
-- Permitted operations are:
-- 1. [Append] Replacing Null with a Node
-- 2. [Logical Deletion] Replacing a Node with a DelNode, preserving the next ptr
-- 3. [Physical Deletion at Node] Replacing a (Node v x) with (Node v y) if x points to (DelNode _ y) (see below)
-- 4. [Physical Deletion at Head] Bumping a Head node's next to the second node (this is a deletion, but I think there's an opt
-- 5. [Insertion at Node]
-- 6. [Insertion at Head]
-- in the delete code that skips the Node -> DelNode transition)
-- Deletion occurs not by replacing a DelNode with something else, but by replacing a Node pointing
-- to a DelNode with a given next pointer with a Node having the same value, and updated (bumped
-- forward) next pointer.  So once a reference points to a DelNode, that's permanent, making the
-- node type and next pointer /stable/.  So with a way to observe the additional stable refinement
-- that a cell has become deleted, I could actually enforce the correct management of next pointers
-- on deletion.
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
-- Also, note the progression of values a given NextPtr points to:
--     a) Null ->
--     b) Node x n ->
--     c) Node x n' -> (where n pointed to (DelNode n') or an insertion occurred); repeat b->c indefinitely
--     c) DelNode x n' ->
--     d) [disconnected]

{-@ any_stable_listrg :: x:Set a -> y:{v:Set a | (SetRG x v)} -> {v:Set a | (v = y)} @-}
any_stable_listrg :: Set a -> Set a -> Set a
any_stable_listrg x y = y

{-@ listrg_refl :: x:Set a -> y:{v:Set a | (SetRG x v)} -> {v:Set a | ((SetRG x y) && (y = v))} @-}
listrg_refl :: Set a -> Set a -> Set a
listrg_refl x y = y
-- TODO: How do I balance < vs <= in p when crossing logically-deleted nodes?
-- TODO: Do i need an Ord a here, for the version that parses?  Or is it treating node_val as a
-- measure rather than a name?
{-@
data Set a <p :: a -> Prop > = 
    Node (node_val :: a<p>) (slack :: { v : a | node_val <= v}) (node_next :: ((RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a))))
  | DelNode (del_val :: a<p>) (slack :: { v : a | del_val <= v}) (del_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a)))
  | Null
  | Head (head_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (1 > 0)}> a)))
@-}
data Set a = Node a a (UNPACK(RGRef (Set a)))
            | DelNode a a (UNPACK(RGRef (Set a)))
            | Null
            | Head (UNPACK(RGRef (Set a))) deriving Eq

{-@ data SetHandle a = SetHandle (lh_head :: IORef (RGRef<{\x -> IsHead x},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a)))
                                 (lh_tail :: IORef (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a))) @-}
data SetHandle a = SetHandle (UNPACK(IORef (RGRef (Set a))))
                             (UNPACK(IORef (RGRef (Set a))))

{-# INLINE myNext #-}
{-@ myNext :: l:Set a -> 
              {r:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> ((IsHead l) || (slack l < x))}> a) |
                   ((nxt l) = r) }
@-}
myNext :: Set a -> RGRef (Set a)
myNext (Node v lb n) = n
myNext (DelNode v lb n) = n
myNext (Head n) = n
myNext _ = error "myNext"

{-@ type InteriorPtr a = RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a) @-}

-- LH seems fine with incomplete pattern matches here,
-- which is great.  It means fewer refinements are added
-- to each constructor, making a lot less work for inference and SMT.
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
{- measure IsHead :: Set a -> Prop
    IsHead (Head n) = true
    IsHead (Node v lb n) = false
    IsHead (DelNode v lb n) = false
    IsHead (Null) = false
-}
{- measure IsNode :: Set a -> Prop
    IsNode (Node v lb n) = true
    IsNode (DelNode v lb n) = false
    IsNode (Null) = false
    IsNode (Head n) = false
-}
{-@ measure val :: Set a -> a
    val (Node v lb n) = v
    val (DelNode v lb n) = v
@-}
{-@ myval :: x:{x:Set a | IsNode x || IsDel x } -> {v:a | v = val x} @-}
myval (Node v lb n) = v
myval (DelNode v lb n) = v
{- measure IsDel :: Set a -> Prop
    IsDel (DelNode v lb n) = true
    IsDel (Null) = false
    IsDel (Head n) = false
    IsDel (Node v lb n) = false
-}
{- measure IsNull :: Set a -> Prop
    IsNull (Null) = true
    IsNull (Head n) = false
    IsNull (Node v lb n) = false
    IsNull (DelNode v lb n) = false
-}
-- A cleaner to show the SMT these predicates are disjoint may be to redefine them as predicates on
-- another measure mapping nodes to some SetTypeEnum...
{-@ assume isDelOnly :: x:Set a -> 
                        {v:Bool | ((IsDel x) <=> ((not (IsHead x)) && (not (IsNull x)) && (not (IsNode x))))} @-}
isDelOnly :: Set a -> Bool
isDelOnly x = True
{-@ assume isNodeOnly :: x:Set a -> 
                        {v:Bool | ((IsNode x) <=> ((not (IsHead x)) && (not (IsNull x)) && (not (IsDel x))))} @-}
isNodeOnly :: Set a -> Bool
isNodeOnly x = True

-- we assume a static head pointer, pointing to the first node which must be Head
-- the deleted field of Head is always False, it's only there to make some of the code
-- more uniform
-- tail points to the last node which must be Null


{-@ type Iterator a = IORef (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a)) @-}
type Iterator a = IORef (RGRef (Set a))


-------------------------------------------
-- auxilliary functions



while b cmd = if b then do {cmd; while b cmd}
              else return ()

repeatUntil cmd = do { b <- cmd; if b then return ()
                                  else repeatUntil cmd }

atomCAS :: Eq a => IORef a -> a -> a -> IO Bool
atomCAS ptr old new =
   atomicModifyIORef ptr (\ cur -> if cur == old
                                   then (new, True)
                                   else (cur, False))

atomicWrite :: IORef a -> a -> IO ()
atomicWrite ptr x =
   atomicModifyIORef ptr (\ _ -> (x,()))


----------------------------------------------
-- functions operating on lists

{-@ dummyRef :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a)) @-}
dummyRef :: (RGRef (Set a))
dummyRef = undefined

{-@ allocNull :: forall <p :: a -> Prop>.
                 IO (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <p> a)) @-}
allocNull :: IO (RGRef (Set a))
allocNull = 
   let memo_null = Null in
   newRGRef memo_null

-- we create a new list
newSet :: IO (SetHandle a)
newSet = 
   --do null <- newRGRef memo_null memo_null any_stable_listrg
   do null <- allocNull
      let memo_hd = Head null 
      hd <- newRGRef memo_hd
      hdPtr <- newIORef hd
      tailPtr <- newIORef null
      return (SetHandle hdPtr tailPtr)


-- Wrap rgCAS with the refinements made concrete, to help inference
{-@ rgSetCAS :: Eq a =>
                 RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a) ->
                 old:(Set a) ->
                 new:{v:(Set a) | (SetRG old v)} ->
                 IO Bool
@-}
rgSetCAS :: Eq a => RGRef (Set a) -> Set a -> Set a -> IO Bool
rgSetCAS r old new = rgCAS r old new --any_stable_listrg

-- I exported pastValue via qualif, but simply defining this fixes qualifier inference....
{-@ readPastValue :: x:InteriorPtr a -> IO ({v:(Set a) | (pastValue x v)}) @-}
readPastValue :: RGRef (Set a) -> IO (Set a)
readPastValue x = readRGRef2 x


{-@ terminal_listrg :: rf:InteriorPtr a -> v:{v:Set a | (IsDel v)}->
                       x:{x:Set a | (x = v)} ->y:{y:Set a | (SetRG x y)} -> {z:Set a | ((x = z) && (z = y))} @-}
terminal_listrg :: RGRef (Set a) -> Set a -> Set a -> Set a -> Set a
terminal_listrg rf v x y = liquidAssume (isDelOnly x) y

{-@ downcast_set :: forall <p :: a -> Prop>. 
                    ref:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <p> a) ->
                    x:a ->
                    {v:(Set <p> a) | pastValue ref v && x < val v } ->
                    {r:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\v -> x < v}> a) | r = ref } @-}
downcast_set :: RGRef (Set a) -> a -> Set a -> RGRef (Set a)
downcast_set r x v = downcast r v

{-@ downcast_set_null :: forall <p :: a -> Prop>. 
                    ref:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <p> a) ->
                    x:a ->
                    {v:(Set <p> a) | pastValue ref v && IsNull v } ->
                    {r:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\v -> x < v}> a) | r = ref } @-}
downcast_set_null :: RGRef (Set a) -> a -> Set a -> RGRef (Set a)
downcast_set_null r x v = downcast r v

{-@ valnode_stable :: forall <q :: a -> Prop>.
                      x:a ->
                      v1:{v:Set<q> a | (IsNode v || IsDel v) && (val v < x) } ->
                      v2:{v:Set<q> a | SetRG v1 v } ->
                      {v:Set<q> a | (IsNode v || IsDel v) && (val v < x) && (v = v2) } @-}
valnode_stable :: a -> Set a -> Set a -> Set a
valnode_stable x v1 v2 = liquidAssume (isDelOnly v1) (liquidAssume (isNodeOnly v1) v2)
-- ^^ could maybe drop the isnode|isdel refinement above if I also injected exclusions for head and
-- null nodes...

{-@ prove_lb :: forall <z :: a -> Prop>.
             ref:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <z> a) ->
             x:a ->
             {n:(Set <z> a)<{\s -> val s < x}> | (IsNode n || IsDel n) && (pastValue ref n) } ->
             {r:RGRef<{\n -> (IsNode n || IsDel n) && val n < x},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <z> a) | r = ref } @-}
prove_lb :: RGRef (Set a) -> a -> Set a -> RGRef (Set a)
prove_lb ref x v = (injectStable ref (v))
--prove_lb ref x v = (injectStable2 (valnode_stable x) ref (v))
-- Above, the q parameter to injectStable seems to be getting chosen as [SetRG v] or [\_-> 1 > 0]
-- depending on whether or not I fully apply injectStable...  can maybe fix by taking explicit
-- stability proof argument like I used to
  --where
  --  {- help :: forall <q :: a -> Prop>.
  --           ref2:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <q> a) ->
  --           {n2:(Set <q> a) | (pastValue ref2 n2) && (val n2 < x) && (IsNode n2) } ->
  --           {r2:RGRef<{\n -> val n < x},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <q> a) | r2 = ref2 } -}
  --  help :: RGRef (Set a) -> Set a -> RGRef (Set a)
  --  help = injectStable

{-@ test_covar :: ref:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\v -> v > 3}> Int) ->
                  {r2:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\v -> v > 1}> Int) | r2 = ref } @-}
test_covar :: RGRef (Set Int) -> RGRef (Set Int)
test_covar ref = safe_covar ref

                




insert :: Ord a => SetHandle a -> a -> IO Bool
insert (SetHandle head _) x =
  do startPtr <- readIORef head
     go startPtr
  where
     -- Note that the RGRef predicate ensures that we're at the start of the list or inserting x just
     -- after prevPtr will preserve sortedness up to that insertion.
     {-@ go :: forall <p :: a -> Prop >.
               RGRef<{\nd -> IsHead nd || val nd < x},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <p> a) -> IO Bool @-}
     go !prevPtr =
        do prevNode <- readRGRef2 prevPtr
           -- note this next line skips over the head 
           let curPtr = myNext prevNode
           curNode <- forgetIOTriple (readRGRef curPtr)
           case curNode of
             Node y lb nextNode ->
                if x == y
                then return False --- already present, not added
                else if y < x
                     then go (prove_lb curPtr x curNode)
                     else --- insertion!  add between previous and current
                        case prevNode of
                          Node prevVal vlb q -> do -- use downcast_set as a form of injectStable that can change parameter instantiation
                                                   -- since Set<{\v -> y < val v}> a <: Set <{\v -> x < val v}> a
                                                   -- doesn't quite fit LH's subtyping schemata
                                                   let newNode = (Node x x (downcast_set curPtr x curNode))
                                                   b <- rgCASpublish newNode prevPtr prevNode (\ptr -> Node prevVal prevVal ptr)
                                                   if b then return True else go prevPtr
                          Head _ -> do let newNode = (Node x x (downcast_set curPtr x curNode))
                                       b <- rgCASpublish newNode prevPtr prevNode (\ptr -> Head ptr)
                                       if b then return True else go prevPtr
                          DelNode _ _ _ -> do newhd <- readIORef head
                                              go newhd -- predecessor deleted, restart
             Null -> case prevNode of
                       Node prevVal vlb q -> do let curPtrC = downcast_set_null curPtr x curNode
                                                let newNode = (Node x x curPtrC)
                                                b <- rgCASpublish newNode prevPtr prevNode (\ptr -> Node prevVal prevVal ptr)
                                                if b then return True else go prevPtr
                       Head _ -> do let newNode = (Node x x (downcast_set_null curPtr x curNode))
                                    b <- rgCASpublish newNode prevPtr prevNode (\ptr -> Head ptr)
                                    if b then return True else go prevPtr
                       DelNode _ _ _ -> do newhd <- readIORef head
                                           go newhd -- predecessor deleted, restart
             DelNode v lb nextNode -> 
                     case prevNode of
                       Node prevVal vlb q -> do let refinedtail = (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) (nextNode))
                                                b <- rgSetCAS prevPtr prevNode (Node prevVal (liquidAssert (prevVal < v) lb) (refinedtail))
                                                go prevPtr -- if b then go prevPtr else go curPtr
                       Head _ -> do b <- rgSetCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                    go prevPtr --if b then go prevPtr else go curPtr
                       DelNode _ _ _ -> do newhd <- readIORef head
                                           go newhd-- predecessor now deleted, need to restart


find :: Ord a => SetHandle a -> a -> IO Bool
find (SetHandle head _) x =
  do startPtr <- readIORef head
     go startPtr
   where
      {-@ go :: forall <p :: a -> Prop >.
                RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <p> a) -> IO Bool @-}
      go !prevPtr =
           do prevNode <-  readRGRef2 prevPtr
              let curPtr = myNext prevNode -- head/node/delnode have all next
              curNode <- forgetIOTriple (readRGRef curPtr)
              case curNode of
                Node y lb nextNode ->
                   if (x == y)
                   then -- node found and alive 
                      return True
                   else go curPtr -- continue
                Null -> return False -- reached end of list; TODO short-circuit based on bounds
                DelNode v lb nextNode -> 
                         -- atomically delete curNode by setting the next of prevNode to next of curNode
                         -- if this fails we simply move ahead
                        case prevNode of
                          Node prevVal vlb q -> do let refinedtail = (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) (nextNode))
                                                   let _ = liquidAssert (q == curPtr) True
                                                   b <- rgSetCAS prevPtr prevNode (Node prevVal (liquidAssert (prevVal < v) lb) (refinedtail))
                                                   if b then go prevPtr else go curPtr
                          Head _ -> do b <- rgSetCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                       if b then go prevPtr else go curPtr
                          DelNode _ _ _ -> go curPtr    -- if parent deleted simply move ahead




delete :: Eq a => SetHandle a -> a -> IO Bool
delete (SetHandle head _) x =
  do startPtr <- readIORef head
     go startPtr
   where
      {-@ go :: RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a) -> IO Bool @-}
      go prevPtr =
        do do prevNode <- forgetIOTriple (readRGRef prevPtr)
              let curPtr = myNext prevNode -- head/node/delnode have all next
              curNode <- forgetIOTriple (readRGRef curPtr)
              case curNode of
                Node y lb nextNode ->
                   if (x == y)
                   then -- node found and alive 
                      do b <- rgSetCAS curPtr curNode (DelNode y lb nextNode)
                         if b then return True
                          else go prevPtr -- spin
                   else go curPtr -- continue
                Null -> return False -- reached end of list; TODO shortcircuit
                DelNode v lb nextNode -> 
                         -- atomically delete curNode by setting the next of prevNode to next of curNode
                         -- if this fails we simply move ahead
                        case prevNode of
                          Node v2 v2lb _ -> do b <- rgSetCAS prevPtr prevNode (Node v2 lb (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                               if b then go prevPtr else go curPtr
                          --Head {} -> do b <- rgSetCAS prevPtr prevNode (Head nextNode)
                          Head _ -> do b <- rgSetCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                       if b then go prevPtr else go curPtr
                          DelNode _ _ _ -> go curPtr    -- if parent deleted simply move ahead



























-- pad html render
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
