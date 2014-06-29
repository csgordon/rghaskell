-- CASList, originally From GHC's test suite (testsuite / tests / concurrent / prog003 / CASList.hs)
-- I rewrote this to use tuples for the node fields instead of records,
-- since LH seems to not support record matching in measure definitions.
-- I'm also concretizing it to a list of Ints, because at the moment
-- Liquid Haskell can't parse type applications in measure ranges
-- (so IORef (List) causes parse errors when writing the next measure).
-- See Liquid Haskell Issue #222 (https://github.com/ucsd-progsys/liquidhaskell/issues/222)

{-# LANGUAGE BangPatterns,CPP #-}
module CASList where

import Control.Monad
import Data.IORef
import Control.Concurrent
import Control.Concurrent.Chan
import System.Environment
import Data.Time

import RG

-- #define USE_UNPACK
-- #define USE_STRICT

#if defined(USE_UNPACK)
#define UNPACK(p) {-# UNPACK #-} !(p)
#elif defined(USE_STRICT)
#define UNPACK(p) !(p)
#else
#define UNPACK(p) p
#endif

{-data List a = Node { val :: a
                   , next :: UNPACK(IORef (List a)) }
            | DelNode { next :: UNPACK(IORef (List a)) }
            | Null
            | Head { next :: UNPACK(IORef (List a)) } deriving Eq

data ListHandle a = ListHandle { headList :: UNPACK(IORef (IORef (List a))), 
                                 tailList :: UNPACK(IORef (IORef (List a))) }
                                 -}
-- Rely/Guarantee for next-pointers:
-- Permitted operations are:
-- 1. Replacing Null with a Node
-- 2. Replacing a Node with a DelNode, preserving the next ptr
-- 3. Replacing a DelNode with the Node at its next pointer
-- 4. Bumping a Head node's next to the second node
{-@ predicate ListRG X Y =
    (((isNull X) && (isNode Y)) ||
     ((isNode X) && (isDel Y) && ((nxt X) = (nxt Y))) ||
     ((isDel X) && (isNode Y)) ||
     ((isHead X) && (isHead Y)) ||
     (X = Y)
     )
@-}
-- TODO: Break out the head case into a separate relation?  The ListHandle
-- has a pointer that is always a head (and could say so in the refinement)
-- while the recursive pointers must never find a head (could say so in
-- the refinement)
-- TODO: Figure out how to enforce that the replacement of the deleted node
-- is actually the correct replacement in 3 and 4.
-- Brief thought: predicate parameters to List which somehow give more information about
-- what's stored at the node's next pointer
-- Also, note the progression of values a given NextPtr points to:
--     a) Null ->
--     b) Node x n ->
--     c) DelNode n ->
--     d) [contents of 

{-@ any_stable_listrg :: x:List -> y:{v:List | (ListRG x v)} -> {v:List | (v = y)} @-}
any_stable_listrg :: List -> List -> List
any_stable_listrg x y = y

{-@
data List = Node (node_val :: Int)
                 (node_next :: ((RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)}> (List))))
            | DelNode (del_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)}> (List)))
            | Null
            | Head (head_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)}> (List)))
@-}
-- <{\x -> (1 > 0)},{\x y -> (ListRG x y)}>
data List = Node Int (UNPACK(RGRef (List)))
            | DelNode (UNPACK(RGRef (List)))
            | Null
            | Head (UNPACK(RGRef (List))) deriving Eq

{-@ data ListHandle = ListHandle (lh_head :: IORef (RGRef (List)))
                                 (lh_tail :: IORef (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)}> (List))) @-}
data ListHandle = ListHandle (UNPACK(IORef (RGRef (List))))
                             (UNPACK(IORef (RGRef (List))))
-- declare a type alias to work around LH issue #222
type NextPtr = RGRef List

{-# INLINE myNext #-}
{-@ myNext :: List -> RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)}> List @-}
myNext :: List -> RGRef (List)
myNext (Node v n) = n
myNext (DelNode n) = n
myNext (Head n) = n
myNext _ = error "myNext"

-- LH seems fine with incomplete pattern matches here,
-- which is great.  It means fewer refinements are added
-- to each constructor, making a lot less work for inference and SMT.
{-@ measure nxt :: List -> NextPtr
    nxt (Node v n) = n
    nxt (DelNode n) = n
    nxt (Head n) = n
@-}
{-@ measure isHead :: List -> Prop
    isHead (Head n) = true
@-}
{-@ measure isNode :: List -> Prop
    isNode (Node v n) = true
@-}
{-@ measure isDel :: List -> Prop
    isDel (DelNode n) = true
@-}
{-@ measure isNull :: List -> Prop
    isNull (Null) = true
@-}

-- we assume a static head pointer, pointing to the first node which must be Head
-- the deleted field of Head is always False, it's only there to make some of the code
-- more uniform
-- tail points to the last node which must be Null


type Iterator = IORef (IORef (List))


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

{-@ assume dropPred :: forall <p :: a -> Prop, r :: a -> a -> Prop>.
                       x:RGRef<p,r> a ->
                       {r:RGRef<{\x -> (1 > 0)},r> a | (x = r)} @-}
dropPred :: RGRef a -> RGRef a
dropPred x = x
{-# INLINE dropPred #-}

{-@ allocNull :: IO (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)}> List) @-}
allocNull :: IO (RGRef List)
allocNull = 
   let memo_null = Null in
   newRGRef memo_null memo_null any_stable_listrg

-- we create a new list
newList :: IO (ListHandle)
newList = 
   --do null <- newRGRef memo_null memo_null any_stable_listrg
   do null <- allocNull
      let memo_hd = Head null 
      hd <- newRGRef memo_hd memo_hd any_stable_listrg
      hdPtr <- newIORef hd
      tailPtr <- newIORef null
      return (ListHandle hdPtr tailPtr)


-- we add a new node, by overwriting the null tail node
-- we only need to adjust tailList but not headList because
-- of the static Head
-- we return the location of the newly added node
addToTail :: ListHandle -> Int -> IO ()
addToTail (ListHandle _ tailPtrPtr) x =
   do null <- let nm = Null in newRGRef nm nm any_stable_listrg
      repeatUntil 
         (do tailPtr <- readIORef tailPtrPtr
             b <- rgCAS tailPtr Null (Node x null) any_stable_listrg
             return b )
        -- we atomically update the tail
        -- (by spinning on the tailPtr)
      atomicWrite tailPtrPtr null


--find :: Eq a => ListHandle a -> a -> IO Bool
--find (ListHandle { headList = head }) x =
--  let go !prevPtr =
--           do prevNode <- readIORef prevPtr
--              let curPtr = myNext prevNode -- head/node/delnode have all next
--              curNode <- readIORef curPtr
--              case curNode of
--                Node {val = y, next = nextNode } ->
--                   if (x == y)
--                   then -- node found and alive 
--                      return True
--                   else go curPtr -- continue
--                Null -> return False -- reached end of list
--                DelNode {next = nextNode } -> 
--                         -- atomically delete curNode by setting the next of prevNode to next of curNode
--                         -- if this fails we simply move ahead
--                        case prevNode of
--                          Node {} -> do b <- atomCAS prevPtr prevNode (Node {val = val prevNode, 
--                                                                             next = nextNode})
--                                        if b then go prevPtr
--                                         else go curPtr
--                          Head {} -> do b <- atomCAS prevPtr prevNode (Head {next = nextNode})
--                                        if b then go prevPtr 
--                                         else go curPtr
--                          DelNode {} -> go curPtr    -- if parent deleted simply move ahead
--             {-
--                correct as well, but a deleted parent deleting a child is (for certain cases) a useless operation
--                                     do atomicModifyIORef prevPtr ( \ cur -> (cur{next = nextNode},True))
--                                        go prevPtr
--              -}
--
--  in do startPtr <- readIORef head
--        go startPtr
--
--
--
--
--delete :: Eq a => ListHandle a -> a -> IO Bool
--delete (ListHandle { headList = head }) x =
--  let go prevPtr =
--        do do prevNode <- readIORef prevPtr
--              let curPtr = next prevNode -- head/node/delnode have all next
--              curNode <- readIORef curPtr
--              case curNode of
--                Node {val = y, next = nextNode } ->
--                   if (x == y)
--                   then -- node found and alive 
--                      do b <- atomCAS curPtr curNode (DelNode {next = nextNode})
--                         if b then return True
--                          else go prevPtr -- spin
--                   else go curPtr -- continue
--                Null -> return False -- reached end of list
--                DelNode {next = nextNode } -> 
--                         -- atomically delete curNode by setting the next of prevNode to next of curNode
--                         -- if this fails we simply move ahead
--                        case prevNode of
--                          Node {} -> do b <- atomCAS prevPtr prevNode (Node {val = val prevNode, 
--                                                                             next = nextNode})
--                                        if b then go prevPtr
--                                         else go curPtr
--                          Head {} -> do b <- atomCAS prevPtr prevNode (Head {next = nextNode})
--                                        if b then go prevPtr 
--                                         else go curPtr
--                          DelNode {} -> go curPtr    -- if parent deleted simply move ahead
--
--  in do startPtr <- readIORef head
--        go startPtr
--
--
--
---- the iterator always points to the PREVIOUS node,
---- recall that there's a static dummy new Head
---- Assumption: iterators are private, 
---- ie they won't be shared among threads
--newIterator :: ListHandle a -> IO (Iterator a)
--newIterator (ListHandle {headList = hd}) =
--  do hdPtr <- readIORef hd
--     it <- newIORef hdPtr
--     return it
--
---- we iterate through the list and return the first "not deleted" node
---- we delink deleted nodes
---- there's no need to adjust headList, tailList
---- cause headList has a static Head and
---- tailList points to Null
--iterateList :: Eq a => Iterator a -> IO (Maybe (IORef (List)))
--iterateList itPtrPtr = 
--  let go prevPtr =
--        do do prevNode <- readIORef prevPtr
--              let curPtr = next prevNode -- head/node/delnode have all next
--              curNode <- readIORef curPtr
--              case curNode of
--                Node {} -> do writeIORef itPtrPtr curPtr 
--                                 -- adjust iterator
--                              return (Just curPtr)
--                Null -> return Nothing -- reached end of list
--                DelNode {next = nextNode} -> 
--                         -- atomically delete curNode by setting the next of prevNode to next of curNode
--                         -- if this fails we simply move ahead
--                        case prevNode of
--                          Node {} -> do b <- atomCAS prevPtr prevNode (Node {val = val prevNode, 
--                                                                             next = nextNode})
--                                        if b then go prevPtr
--                                         else go curPtr
--                          Head {} -> do b <- atomCAS prevPtr prevNode (Head {next = nextNode})
--                                        if b then go prevPtr 
--                                         else go curPtr
--                          DelNode {} -> go curPtr    -- if parent deleted simply move ahead
--
--  in do startPtr <- readIORef itPtrPtr
--        go startPtr
--
--
----printing and counting
--
--printList :: Show a => ListHandle a -> IO ()
--printList (ListHandle {headList = ptrPtr}) =
--  do startptr <- (
--          do ptr <- readIORef ptrPtr
--             Head {next = startptr} <- readIORef ptr
--             return startptr)
--     printListHelp startptr
--
--
--printListHelp :: Show a => IORef (List) -> IO ()
--printListHelp curNodePtr =
--   do { curNode <- readIORef curNodePtr
--      ; case curNode of
--          Null -> putStr "Nil"
--          Node {val = curval, next = curnext} ->
--             do { putStr (show curval  ++ " -> ")
--                ;  printListHelp curnext }
--          DelNode {next = curnext} ->
--             do { putStr ("DEAD -> ")
--                ;  printListHelp curnext }
--      } 
--
--cntList :: Show a => ListHandle a -> IO Int
--cntList (ListHandle {headList = ptrPtr}) =
--  do startptr <- (
--          do ptr <- readIORef ptrPtr
--             Head {next = startptr} <- readIORef ptr
--             return startptr)
--     cntListHelp startptr 0
--
--
--cntListHelp :: Show a => IORef (List) -> Int -> IO Int
--cntListHelp curNodePtr i =
--   do { curNode <- readIORef curNodePtr
--      ; case curNode of
--          Null -> return i
--          Node {val = curval, next = curnext} -> 
--                cntListHelp curnext (i+1)
--          DelNode {next = curnext} ->
--                cntListHelp curnext (i+1)
--      } 
--
---- Whitespace to the popups in the HTML render are readable
--
--
--
--
--
--
--
--
