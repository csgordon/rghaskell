-- Originally from Control.Sequential.STM
-- https://github.com/ghc/packages-stm/blob/master/Control/Sequential/STM.hs
-- Note that this is *NOT* the actual STM implementation, which is really defined in
--     https://github.com/ghc/ghc/blob/master/libraries/base/GHC/Conc/Sync.lhs
-- in terms of some GHC primitives (intrinsics).  This module is the fallback code for when you
-- compile STM code with another Haskell compiler with no STM runtime support (so it must correctly
-- implement an undo log)
--
--
-- Transactional memory for sequential implementations.
-- Transactions do not run concurrently, but are atomic in the face
-- of exceptions.

{-# LANGUAGE CPP #-}

#if __GLASGOW_HASKELL__ >= 701
{-# LANGUAGE Trustworthy #-}
#endif

-- #hide
module STMLog (
STM, --atomically, throwSTM, catchSTM,
--TVar, newTVar, newTVarIO, readTVar, readTVarIO, writeTVar
    ) where

#if __GLASGOW_HASKELL__ < 705
import Prelude hiding (catch)
#endif
import Control.Applicative (Applicative(pure, (<*>)))
import Control.Exception
import Data.IORef
import RG
import GHC.Base
import Language.Haskell.Liquid.Prelude

-- LH can't parse >> for sequencing, and we need to export some axioms anyways
-- Can't mention seqIOUnit in axioms, so I'm baking the left unit property into its type
{-@ predicate Delta x y = 1 > 0 @-}
{- TODO: I think exists isn't allowed /inside/ a predicate.  So I need a measure
 -     fwd_extends :: IO () -> IO () -> Prop
 - with axioms
 -     assume fwd_extends_refl :: m:IO () -> {v:Bool | (fwd_extends m m)}
 -     assume fwd_extends_trans :: a:IO () -> 
 -                                 b:{x:IO () | (fwd_extends a b)} ->
 -                                 c:{x:IO () | (fwd_extends b c)} ->
 -                                 {v:Bool | (fwd_extends a c)}
 - and typing seqIOUnit as
 -     assume seqIOUnit :: IO () -> m:IO () -> {a:IO () | (fwd_extends a m)}
 -     (or equivalent axiom)
 -}
{-@ measure fwd_extends :: IO () -> IO () -> Prop @-}
{-@ assume fwd_extends_refl :: m:IO () -> {v:Bool | (fwd_extends m m)} @-}
fwd_extends_refl :: IO () -> Bool
fwd_extends_refl = undefined
{-@ assume fwd_extends_trans :: a:IO () -> 
                                b:{x:IO () | (fwd_extends a x)} ->
                                c:{x:IO () | (fwd_extends b x)} ->
                                {v:Bool | (fwd_extends a c)} @-}
fwd_extends_trans :: IO () -> IO () -> IO () -> Bool
fwd_extends_trans x y z = undefined

{-@ assume seqIOUnit :: IO () -> m:IO () -> {a:IO () | (fwd_extends a m)} @-}
seqIOUnit :: IO () -> IO () -> IO ()
seqIOUnit a b = a >>= (\_ -> b)

{-@ test_extends_refl :: {a:IO () | (fwd_extends a a)} @-}
test_extends_refl :: IO ()
test_extends_refl = let a = return () in -- must bind to equate the actions
                    liquidAssume (fwd_extends_refl a) a
{-@ test_extends_trans :: a:IO () -> b:IO () -> c:IO () -> {x:IO () | (fwd_extends x c)} @-}
test_extends_trans :: IO () -> IO () -> IO () -> IO ()
test_extends_trans a b c = let ab = seqIOUnit a b in -- fwd_extends a b
                           let abc = seqIOUnit ab c in -- fwd_extends ab c
                           abc --liquidAssume (fwd_extends_trans abc) abc
-- Test the construction used in the ref update in writeTVar
{-@ test_partial :: IO () -> b:IO () -> {x:IO () | (fwd_extends x b)} @-}
test_partial :: IO () -> IO () -> IO ()
test_partial a = seqIOUnit a


-- The reference contains a rollback action to be executed on exceptions
{- data STM a = STM (stm_log_ref :: 
   (RGRef<{\x -> (true)},{\x y -> (exists[f:(IO ())].(y = (seqIOUnit f x)))}> (IO ()) -> IO a)) -}
{-@ data STM a = STM (stm_log_ref :: (RGRef<{\x -> (true)},{\x y -> (fwd_extends y x)}> (IO ()) -> IO a)) @-}
{- data STM a = STM (stm_log_ref :: (RGRef<{\x -> (true)},{\x y -> (1 > 0)}> (IO ()) -> IO a)) @-}
data STM a = STM (RGRef (IO ()) -> IO a)
-- STM should be a newtype, but I can't figure out how to make LH refine newtypes

{-@ unSTM :: STM a -> RGRef<{\ x -> 1 > 0},{\x y -> (fwd_extends y x)}> (IO ()) -> IO a @-}
unSTM :: STM a -> RGRef (IO ()) -> IO a
unSTM (STM f) = f

instance Functor STM where
    fmap f (STM m) = STM (fmap f . m)

instance Applicative STM where
    pure = STM . const . pure
    STM mf <*> STM mx = STM $ \ r -> mf r <*> mx r

instance Monad STM where
    return = pure
    STM m >>= k = STM $ \ r -> do
                                x <- m r
                                unSTM (k x) r

{-@ data StabilityPf a <p :: a -> Prop, r :: a -> a -> Prop> =
	Stable (stability_proof :: (x:a<p> -> y:a<r x> -> {z:a<p> | z = y})) @-}
data StabilityPf a = Stable (a -> a -> a)
{- fetch_proof :: forall <p :: a -> Prop, r :: a -> a -> Prop>.
                          StabilityPf<p,r> a ->
                          (x:a<p> -> y:a<r x> -> {z:a<p> | z = y}) @-}
--fetch_proof (Stable pf) = pf  -- The inferred type of pf looks like the refinements aren't quite right...

{-@ stbl :: x:(IO ()) ->
            y:{y:(IO ()) | (fwd_extends y x)} ->
            {z:(IO ()) | z = y} @-}
stbl :: IO () -> IO () -> IO ()
stbl x y = y

{-@ freshSTMRef :: () -> IO (RGRef<{\x -> (1 > 0)},{\x y -> (fwd_extends y x)}> (IO ())) @-}
freshSTMRef :: () -> IO (RGRef (IO ()))
freshSTMRef _ = 
    -- Remember, return () behaves /generatively/ w.r.t. identity in the refinement language!
    -- TODO: Note in writeups that this generative behavior is important, and this binding is
    -- critical to getting relations to be inferred correctly
    let x = return () in
    newRGRef x (return () `seqIOUnit` x) (\x y -> y)


{-@ atomically :: STM a -> IO a @-}
atomically :: STM a -> IO a
atomically (STM m) = do
                        --r <- newRGRef (return ()) (return ()) stbl -- actually, rely is not reflexive
                        r <- freshSTMRef ()
                        m r `onException` do
                                            --rollback <- readRGRef r
                                            --(forgetIOTriple (readRGRef r)) `bindIO` (\rollback -> rollback)
                                            rollback <- forgetIOTriple (readRGRef r)
                                            rollback

-- If we leave this alone, it will infer throwSTM :: forall a b. Exception a => {x:a | false} -> STM b
-- So we have to repeat the Haskell type explicitly for LH so it will infer inhabitable refinements
{-@ throwSTM :: Exception e => e -> STM a @-}
throwSTM :: Exception e => e -> STM a
throwSTM = STM . const . throwIO

{-@ catchSTM :: Exception e => STM a -> (e -> STM a) -> STM a @-}
catchSTM :: Exception e => STM a -> (e -> STM a) -> STM a
--catchSTM (STM m) h = STM $ \ r -> do
catchSTM (STM m) h = STM body
    where
    {-@ body :: RGRef<{\x -> (true)},{\x y -> (fwd_extends y x)}> (IO ()) -> IO a @-}
    --body :: RGRef (IO ()) -> IO a
    body r = do
        --old_rollback <- readIORef r
        --writeIORef r (return ())
        --r2 <- newIORef (return ())
        --r2 <- newRGRef (return ()) (return ()) (\ x y -> y) -- actually, rely is not reflexive
        r2 <- freshSTMRef ()
        --res <- try (m r)
        res <- try (m r2)
        rollback_m <- forgetIOTriple (readRGRef r2)
        --rollback_m <- readIORef r
        case res of
            Left ex -> do
                            rollback_m
                            --writeIORef r old_rollback
                            unSTM (h ex) r
            Right a -> do
                            --writeIORef r (rollback_m >> old_rollback)
                            --modifyRGRef r (\ old_rollback -> (rollback_m >> old_rollback)) (\ x y -> y)
                            modifyRGRef r (\ old_rollback -> (rollback_m `seqIOUnit` old_rollback)) (\ x y -> y)
                            return a

newtype TVar a = TVar (IORef a)
    deriving (Eq)

{-@ newTVar :: a -> STM (TVar a) @-}
newTVar :: a -> STM (TVar a)
newTVar a = STM (const (newTVarIO a))

{-@ newTVarIO :: a -> IO (TVar a) @-}
newTVarIO :: a -> IO (TVar a)
newTVarIO a = do
    ref <- newIORef a
    return (TVar ref)

{-@ readTVar :: TVar a -> STM a @-}
readTVar :: TVar a -> STM a
readTVar (TVar ref) = STM (const (readIORef ref))

{-@ readTVarIO :: TVar a -> IO a @-}
readTVarIO :: TVar a -> IO a
readTVarIO (TVar ref) = readIORef ref

{-@ writeTVar :: TVar a -> a -> STM () @-}
writeTVar :: TVar a -> a -> STM ()
--writeTVar (TVar ref) a = STM $ \ r -> do
writeTVar (TVar ref) a = STM body
    where 
    {-@ body :: RGRef<{\x -> (true)},{\x y -> (fwd_extends y x)}> (IO ()) -> IO () @-}
    body :: RGRef (IO ()) -> IO ()
    body r = do
        oldval <- readIORef ref
        --modifyRGRef r (writeIORef ref oldval >>) (\x y -> y)
        modifyRGRef r (writeIORef ref oldval `seqIOUnit`) (\x y -> y)
        writeIORef ref a
        






