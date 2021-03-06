-- CASList, originally From GHC's test suite (testsuite / tests / concurrent / prog003 / CASList.hs)
-- I rewrote this to use tuples for the node fields instead of records,
-- since LH seems to not support record matching in measure definitions.

{-# LANGUAGE BangPatterns,CPP #-}
-- Disable termination checking; this is lock-free, not wait-free
{-@ LIQUID "--no-termination" @-}
module CASList where

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
-- 1. [Append] Replacing Null with a Node
-- 2. [Logical Deletion] Replacing a Node with a DelNode, preserving the next ptr
-- 3. [Physical Deletion at Node] Replacing a (Node v x) with (Node v y) if x points to (DelNode y) (see below)
-- 4. [Physical Deletion at Head] Bumping a Head node's next to the second node (this is a deletion, but I think there's an opt
-- in the delete code that skips the Node -> DelNode transition)
-- Deletion occurs not by replacing a DelNode with something else, but by replacing a Node pointing
-- to a DelNode with a given next pointer with a Node having the same value, and updated (bumped
-- forward) next pointer.  So once a reference points to a DelNode, that's permanent, making the
-- node type and next pointer /stable/.  So with a way to observe the additional stable refinement
-- that a cell has become deleted, I could actually enforce the correct management of next pointers
-- on deletion.
{-@ predicate ListRG X Y =
    (((isNull X) && (isNode Y)) ||
     ((isNode X) && (isDel Y) && ((nxt X) = (nxt Y))) ||
     ((isNode X) && (isNode Y) && (isDel (terminalValue (nxt X))) && ((val X) = (val Y)) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     ((isHead X) && (isHead Y) && (isDel (terminalValue (nxt X))) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     (X = Y)
     )
@-}
-- Also, note the progression of values a given NextPtr points to:
--     a) Null ->
--     b) Node x n ->
--     c) Node x n' -> (where n pointed to (DelNode n')); repeat b->c indefinitely
--     c) DelNode n' ->
--     d) [disconnected]

{-@ any_stable_listrg :: x:List a -> y:{v:List a | (ListRG x v)} -> {v:List a | (v = y)} @-}
any_stable_listrg :: List a -> List a -> List a
any_stable_listrg x y = y

{-@ listrg_refl :: x:List a -> y:{v:List a | (ListRG x v)} -> {v:List a | ((ListRG x y) && (y = v))} @-}
listrg_refl :: List a -> List a -> List a
listrg_refl x y = y

{-@
data List a = Node (node_val :: a)
                 (node_next :: ((RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a))))
            | DelNode (del_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a)))
            | Null
            | Head (head_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a)))
@-}
-- <{\x -> (1 > 0)},{\x y -> (ListRG x y)}>
data List a = Node a (UNPACK(RGRef (List a)))
            | DelNode (UNPACK(RGRef (List a)))
            | Null
            | Head (UNPACK(RGRef (List a))) deriving Eq

{-@ data ListHandle a = ListHandle (lh_head :: IORef (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a)))
                                 (lh_tail :: IORef (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a))) @-}
data ListHandle a = ListHandle (UNPACK(IORef (RGRef (List a))))
                             (UNPACK(IORef (RGRef (List a))))

{-# INLINE myNext #-}
{-@ myNext :: l:List a -> 
              {r:RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a) |
                   ((nxt l) = r) }
@-}
myNext :: List a -> RGRef (List a)
myNext (Node v n) = n
myNext (DelNode n) = n
myNext (Head n) = n
myNext _ = error "myNext"

{-@ type InteriorPtr a = RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a) @-}

-- LH seems fine with incomplete pattern matches here,
-- which is great.  It means fewer refinements are added
-- to each constructor, making a lot less work for inference and SMT.
{-@ measure nxt :: List a -> (RGRef (List a))
    nxt (Node v n) = n
    nxt (DelNode n) = n
    nxt (Head n) = n
@-}
{-@ measure isHead :: List a -> Prop
    isHead (Head n) = true
@-}
{-@ measure isNode :: List a -> Prop
    isNode (Node v n) = true
@-}
{-@ measure val :: List a -> a
    val (Node v n) = v
@-}
{-@ measure isDel :: List a -> Prop
    isDel (DelNode n) = true
@-}
{-@ measure isNull :: List a -> Prop
    isNull (Null) = true
@-}
-- A cleaner to show the SMT these predicates are disjoint may be to redefine them as predicates on
-- another measure mapping nodes to some ListTypeEnum...
{-@ assume isDelOnly :: x:List a -> 
                        {v:Bool | ((isDel x) <=> ((not (isHead x)) && (not (isNull x)) && (not (isNode x))))} @-}
isDelOnly :: List a -> Bool
isDelOnly x = undefined

-- we assume a static head pointer, pointing to the first node which must be Head
-- the deleted field of Head is always False, it's only there to make some of the code
-- more uniform
-- tail points to the last node which must be Null


{-@ type Iterator a = IORef (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a)) @-}
type Iterator a = IORef (RGRef (List a))


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

{-@ dummyRef :: (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a)) @-}
dummyRef :: (RGRef (List a))
dummyRef = undefined

{-@ allocNull :: IO (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a)) @-}
allocNull :: IO (RGRef (List a))
allocNull = 
   let memo_null = Null in
   newRGRef memo_null

-- we create a new list
newList :: IO (ListHandle a)
newList = 
   --do null <- newRGRef memo_null memo_null any_stable_listrg
   do null <- allocNull
      let memo_hd = Head null 
      hd <- newRGRef memo_hd
      hdPtr <- newIORef hd
      tailPtr <- newIORef null
      return (ListHandle hdPtr tailPtr)


-- we add a new node, by overwriting the null tail node
-- we only need to adjust tailList but not headList because
-- of the static Head
-- we return the location of the newly added node
addToTail :: Eq a => ListHandle a -> a -> IO ()
addToTail (ListHandle _ tailPtrPtr) x =
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
{-@ rgListCAS :: Eq a =>
                 RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a) ->
                 old:(List a) ->
                 new:{v:(List a) | (ListRG old v)} ->
                 IO Bool
@-}
rgListCAS :: Eq a => RGRef (List a) -> List a -> List a -> IO Bool
rgListCAS r old new = rgCAS r old new --any_stable_listrg

-- I exported pastValue via qualif, but simply defining this fixes qualifier inference....
{-@ readPastValue :: x:InteriorPtr a -> IO ({v:(List a) | (pastValue x v)}) @-}
readPastValue :: RGRef (List a) -> IO (List a)
readPastValue x = readRGRef2 x


{-@ terminal_listrg :: rf:InteriorPtr a -> v:{v:List a | (isDel v)}->
                       x:{x:List a | (x = v)} ->y:{y:List a | (ListRG x y)} -> {z:List a | ((x = z) && (z = y))} @-}
terminal_listrg :: RGRef (List a) -> List a -> List a -> List a -> List a
terminal_listrg rf v x y = liquidAssume (isDelOnly x) y


find :: Eq a => ListHandle a -> a -> IO Bool
find (ListHandle head _) x =
  do startPtr <- readIORef head
     go startPtr
   where
      {-@ go :: RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a) -> IO Bool @-}
      go !prevPtr =
           do prevNode <-  readRGRef2 prevPtr
              --prevNode2 <- readRGRef2 prevPtr
              readRGRef2 prevPtr >>= (return . (typecheck_pastval prevPtr))
              _ <- return (typecheck_pastval prevPtr prevNode)
              --_ <- return (typecheck_pastval prevPtr prevNode2)
              let curPtr = myNext prevNode -- head/node/delnode have all next
              curNode <- forgetIOTriple (readRGRef curPtr)
-- ## curNode :: { v : List a | pastValue curPtr v }
              case curNode of
                Node y nextNode ->
                   if (x == y)
                   then -- node found and alive 
                      return True
                   else go curPtr -- continue
                Null -> return False -- reached end of list
                DelNode nextNode -> 
-- ## Now curNode=(DelNode nextNode), which is stable w.r.t. ListRG.
-- ## We get this as a refinement on a value s.t. pastValue curPtr curNode, so by SMT congruence,
-- ## pastValue curPtr (DelNode nextNode)
-- ## I'd be willing to specialize the field observation of "terminal states" if necessary, since
-- ## that's at least pretty general.
-- ## Need measure terminalValue :: RGRef a -> a
-- ## Need axiom pastIsTerminal :: r:RGRef<p,r> a -> v:a ->
--                                 pf(x:{x:a | x = v} -> y:a<r x> -> {z:a | z = y && z = x}) ->
--                                 {b:Bool | (((terminalValue r) = v) <=> (pastValue r v))}
                         -- atomically delete curNode by setting the next of prevNode to next of curNode
                         -- if this fails we simply move ahead
                        case prevNode of
                          -- TODO: Do I actually need rgListCAS here to get the types right, or did
                          -- using it just help inference give a better / more local error report?
                          Node prevVal _ -> do b <- rgListCAS prevPtr prevNode (Node prevVal (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                               if b then go prevPtr else go curPtr
                          --Next line typechecks fine, switched to rgListCAS for consistency and to
                          --ensure rgListCAS wasn't breaking some useful inference
                          --Head _ -> do b <- rgCAS prevPtr prevNode (Head nextNode) any_stable_listrg
                          --Head _ -> do b <- rgListCAS prevPtr prevNode (Head nextNode)
                          Head _ -> do b <- rgListCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                       if b then go prevPtr else go curPtr
                          DelNode _ -> go curPtr    -- if parent deleted simply move ahead
             {-
                correct as well, but a deleted parent deleting a child is (for certain cases) a useless operation
                                     do atomicModifyIORef prevPtr ( \ cur -> (cur{next = nextNode},True))
                                        go prevPtr
              -}

  --in do startPtr <- readIORef head
  --      go startPtr




delete :: Eq a => ListHandle a -> a -> IO Bool
delete (ListHandle head _) x =
  do startPtr <- readIORef head
     go startPtr
   where
      {-@ go :: RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a) -> IO Bool @-}
      go prevPtr =
        do do prevNode <- forgetIOTriple (readRGRef prevPtr)
              let curPtr = myNext prevNode -- head/node/delnode have all next
              curNode <- forgetIOTriple (readRGRef curPtr)
              case curNode of
                Node y nextNode ->
                   if (x == y)
                   then -- node found and alive 
                      do b <- rgListCAS curPtr curNode (DelNode nextNode)
                         if b then return True
                          else go prevPtr -- spin
                   else go curPtr -- continue
                Null -> return False -- reached end of list
                DelNode nextNode -> 
                         -- atomically delete curNode by setting the next of prevNode to next of curNode
                         -- if this fails we simply move ahead
                        case prevNode of
                          Node v _ -> do b <- rgListCAS prevPtr prevNode (Node v (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                         if b then go prevPtr else go curPtr
                          --Head {} -> do b <- rgListCAS prevPtr prevNode (Head nextNode)
                          Head _ -> do b <- rgListCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                       if b then go prevPtr else go curPtr
                          DelNode {} -> go curPtr    -- if parent deleted simply move ahead

  --in do startPtr <- readIORef head
  --      go startPtr



-- the iterator always points to the PREVIOUS node,
-- recall that there's a static dummy new Head
-- Assumption: iterators are private, 
-- ie they won't be shared among threads
{-@ newIterator :: ListHandle a -> IO (Iterator a) @-} -- <-- This use of Iterator is a LH alias
newIterator :: ListHandle a -> IO (Iterator a)
newIterator (ListHandle hd _) =
  do hdPtr <- readIORef hd
     it <- (newIORef hdPtr)
     return it

-- we iterate through the list and return the first "not deleted" node
-- we delink deleted nodes
-- there's no need to adjust headList, tailList
-- cause headList has a static Head and
-- tailList points to Null
-- Again, Iterator in the LH type is a LH type alias
{-@ iterateList :: Eq a => Iterator a -> IO (Maybe (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a))) @-}
iterateList :: Eq a => Iterator a -> IO (Maybe (RGRef (List a)))
iterateList itPtrPtr = 
  do startPtr <- readIORef itPtrPtr
     go startPtr
   where
      {-@ go :: RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a) -> IO (Maybe (RGRef<{\x -> (1 > 0)},{\x y -> (ListRG x y)},{\x y -> (ListRG x y)}> (List a))) @-}
      go prevPtr =
        do do prevNode <- forgetIOTriple (readRGRef prevPtr)
              let curPtr = myNext prevNode -- head/node/delnode have all next
              curNode <- forgetIOTriple (readRGRef curPtr)
              case curNode of
                Node _ _ -> do writeIORef itPtrPtr curPtr 
                                 -- adjust iterator
                               return (Just curPtr)
                Null -> return Nothing -- reached end of list
                DelNode nextNode -> 
                         -- atomically delete curNode by setting the next of prevNode to next of curNode
                         -- if this fails we simply move ahead
                        case prevNode of
                          Node v _ -> do b <- rgListCAS prevPtr prevNode (Node v (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                         if b then go prevPtr else go curPtr
                          --Head _ -> do b <- rgListCAS prevPtr prevNode (Head nextNode)
                          Head _ -> do b <- rgListCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                       if b then go prevPtr else go curPtr
                          DelNode _ -> go curPtr    -- if parent deleted simply move ahead

  --in do startPtr <- readIORef itPtrPtr
  --      go startPtr


--printing and counting

printList :: Show a => ListHandle a -> IO ()
printList (ListHandle ptrPtr _) =
  do startptr <- (
          do ptr <- readIORef ptrPtr
             Head startptr <- forgetIOTriple (readRGRef ptr)
             return startptr)
     printListHelp startptr

{-@ printListHelp :: Show a => InteriorPtr a -> IO () @-}
printListHelp :: Show a => RGRef (List a) -> IO ()
printListHelp curNodePtr =
   do { curNode <- forgetIOTriple (readRGRef curNodePtr)
      ; case curNode of
          Null -> putStr "Nil"
          Node curval curnext ->
             do { putStr (show curval  ++ " -> ")
                ;  printListHelp curnext }
          DelNode curnext ->
             do { putStr ("DEAD -> ")
                ;  printListHelp curnext }
      } 

-- I've left these commented out; the uses of addition in cntListHelp are failing because some weird
-- bound gets picked up for the formal parameter...
--cntList :: Show a => ListHandle a -> IO Int
--cntList (ListHandle ptrPtr _) =
--  do startptr <- (
--          do ptr <- readIORef ptrPtr
--             Head startptr <- forgetIOTriple (readRGRef ptr)
--             return startptr)
--     cntListHelp startptr 0
--
--
--{- cntListHelp :: Show a => InteriorPtr a -> Int -> IO Int @-}
--cntListHelp :: Show a => RGRef (List a) -> Int -> IO Int
--cntListHelp curNodePtr i =
--   do { curNode <- forgetIOTriple (readRGRef curNodePtr)
--      ; case curNode of
--          Null -> return i
--          Node curval curnext -> 
--                cntListHelp curnext (i+1)
--          DelNode curnext ->
--                cntListHelp curnext (i+1)
--      } 
--
-- Whitespace to the popups in the HTML render are readable
-- Dots to allow scrolling far to the
-- right............................................................................................................................................................................................................................................................................................................................







