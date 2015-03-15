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
-- in the delete code that skips the Node -> DelNode transition)
-- Deletion occurs not by replacing a DelNode with something else, but by replacing a Node pointing
-- to a DelNode with a given next pointer with a Node having the same value, and updated (bumped
-- forward) next pointer.  So once a reference points to a DelNode, that's permanent, making the
-- node type and next pointer /stable/.  So with a way to observe the additional stable refinement
-- that a cell has become deleted, I could actually enforce the correct management of next pointers
-- on deletion.
{-@ predicate SetRG X Y =
    (((isNull X) && (isNode Y)) ||
     ((isNode X) && (isDel Y) && ((val X) = (val Y)) && ((nxt X) = (nxt Y))) ||
     ((isNode X) && (isNode Y) && (isDel (terminalValue (nxt X))) && ((val X) = (val Y)) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     ((isHead X) && (isHead Y) && (isDel (terminalValue (nxt X))) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     (X = Y)
     )
@-}
-- Also, note the progression of values a given NextPtr points to:
--     a) Null ->
--     b) Node x n ->
--     c) Node x n' -> (where n pointed to (DelNode n')); repeat b->c indefinitely
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
    Node (node_val :: a<p>) (node_next :: ((RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (node_val < x)}> a))))
  | DelNode (del_val :: a<p>) (del_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (del_val < x)}> a)))
  | Null
  | Head (head_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (1 > 0)}> a)))
@-}
data Set a = Node a (UNPACK(RGRef (Set a)))
            | DelNode a (UNPACK(RGRef (Set a)))
            | Null
            | Head (UNPACK(RGRef (Set a))) deriving Eq

{-@ data SetHandle a = SetHandle (lh_head :: IORef (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a)))
                                 (lh_tail :: IORef (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a))) @-}
data SetHandle a = SetHandle (UNPACK(IORef (RGRef (Set a))))
                             (UNPACK(IORef (RGRef (Set a))))

{-# INLINE myNext #-}
{-@ myNext :: l:Set a -> 
              {r:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a) |
                   ((nxt l) = r) }
@-}
myNext :: Set a -> RGRef (Set a)
myNext (Node v n) = n
myNext (DelNode v n) = n
myNext (Head n) = n
myNext _ = error "myNext"

{-@ type InteriorPtr a = RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a) @-}

-- LH seems fine with incomplete pattern matches here,
-- which is great.  It means fewer refinements are added
-- to each constructor, making a lot less work for inference and SMT.
{-@ measure nxt :: Set a -> (RGRef (Set a))
    nxt (Node v n) = n
    nxt (DelNode v n) = n
    nxt (Head n) = n
@-}
{-@ measure isHead :: Set a -> Prop
    isHead (Head n) = true
@-}
{-@ measure isNode :: Set a -> Prop
    isNode (Node v n) = true
@-}
{-@ measure val :: Set a -> a
    val (Node v n) = v
    val (DelNode v n) = v
@-}
{-@ measure isDel :: Set a -> Prop
    isDel (DelNode v n) = true
@-}
{-@ measure isNull :: Set a -> Prop
    isNull (Null) = true
@-}
-- A cleaner to show the SMT these predicates are disjoint may be to redefine them as predicates on
-- another measure mapping nodes to some SetTypeEnum...
{-@ assume isDelOnly :: x:Set a -> 
                        {v:Bool | ((isDel x) <=> ((not (isHead x)) && (not (isNull x)) && (not (isNode x))))} @-}
isDelOnly :: Set a -> Bool
isDelOnly x = undefined

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


-- we add a new node, by overwriting the null tail node
-- we only need to adjust tailSet but not headSet because
-- of the static Head
-- we return the location of the newly added node
addToTail :: Eq a => SetHandle a -> a -> IO ()
addToTail (SetHandle _ tailPtrPtr) x =
   --do null <- let nm = Null in newRGRef nm nm any_stable_listrg
   do null <- allocNull
      repeatUntil 
         (do tailPtr <- readIORef tailPtrPtr
             b <- rgCAS tailPtr Null (Node x null) --any_stable_listrg
             return b )
        -- we atomically update the tail
        -- (by spinning on the tailPtr)
      atomicWrite tailPtrPtr null

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


{-@ terminal_listrg :: rf:InteriorPtr a -> v:{v:Set a | (isDel v)}->
                       x:{x:Set a | (x = v)} ->y:{y:Set a | (SetRG x y)} -> {z:Set a | ((x = z) && (z = y))} @-}
terminal_listrg :: RGRef (Set a) -> Set a -> Set a -> Set a -> Set a
terminal_listrg rf v x y = liquidAssume (isDelOnly x) y


find :: Eq a => SetHandle a -> a -> IO Bool
find (SetHandle head _) x =
  do startPtr <- readIORef head
     go startPtr
   where
      {-@ go :: forall <p :: a -> Prop >.
                RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <p> a) -> IO Bool @-}
      go !prevPtr =
           do prevNode <-  readRGRef2 prevPtr
              --prevNode2 <- readRGRef2 prevPtr
              readRGRef2 prevPtr >>= (return . (typecheck_pastval prevPtr))
              _ <- return (typecheck_pastval prevPtr prevNode)
              --_ <- return (typecheck_pastval prevPtr prevNode2)
              let curPtr = myNext prevNode -- head/node/delnode have all next
              curNode <- forgetIOTriple (readRGRef curPtr)
              case curNode of
                Node y nextNode ->
                   if (x == y)
                   then -- node found and alive 
                      return True
                   else go curPtr -- continue
                Null -> return False -- reached end of list
                DelNode v nextNode -> 
                         -- atomically delete curNode by setting the next of prevNode to next of curNode
                         -- if this fails we simply move ahead
                        case prevNode of
                          Node prevVal _ -> do let refinedtail = (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode)
                                               b <- rgSetCAS prevPtr prevNode (Node prevVal refinedtail)
                                               if b then go prevPtr else go curPtr
                          Head _ -> do b <- rgSetCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                       if b then go prevPtr else go curPtr
                          DelNode _ _ -> go curPtr    -- if parent deleted simply move ahead




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
                Node y nextNode ->
                   if (x == y)
                   then -- node found and alive 
                      do b <- rgSetCAS curPtr curNode (DelNode y nextNode)
                         if b then return True
                          else go prevPtr -- spin
                   else go curPtr -- continue
                Null -> return False -- reached end of list
                DelNode v nextNode -> 
                         -- atomically delete curNode by setting the next of prevNode to next of curNode
                         -- if this fails we simply move ahead
                        case prevNode of
                          Node v _ -> do b <- rgSetCAS prevPtr prevNode (Node v (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                         if b then go prevPtr else go curPtr
                          --Head {} -> do b <- rgSetCAS prevPtr prevNode (Head nextNode)
                          Head _ -> do b <- rgSetCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                       if b then go prevPtr else go curPtr
                          DelNode _ _ -> go curPtr    -- if parent deleted simply move ahead

  --in do startPtr <- readIORef head
  --      go startPtr



























