-- Originally from Control.Sequential.STM
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

-- LH can't parse >> for sequencing, and we need to export some axioms anyways
-- Can't mention seqIOUnit in axioms, so I'm baking the left unit property into its type
{- assume seqIOUnit :: a:IO () -> b:IO () -> {m:IO () | ((a = (return ())) => m = b)} @-}
seqIOUnit :: IO () -> IO () -> IO ()
seqIOUnit a b = a >>= (\_ -> b)
{-@ assume axiom_left_unit_bind :: ret:(IO ()) ->
                            seq:(IO () -> IO () -> IO ()) ->
                            m:IO () -> {v : Bool | ((seq ret m) = m)} @-}
axiom_left_unit_bind :: (IO ()) -> (IO () -> IO () -> IO ()) -> IO () -> Bool
axiom_left_unit_bind ret bind m = undefined
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
-- The reference contains a rollback action to be executed on exceptions
{- data STM a = STM (stm_log_ref :: 
   (RGRef<{\x -> (true)},{\x y -> (exists[f:(IO ())].(y = (seqIOUnit f x)))}> (IO ()) -> IO a)) -}
{-@ data STM a = STM (stm_log_ref :: (RGRef<{\x -> (true)},{\x y -> (1 > 0)}> (IO ()) -> IO a)) @-}
data STM a = STM (RGRef (IO ()) -> IO a)
-- STM should be a newtype, but I can't figure out how to make LH refine newtypes


{-@ unSTM :: STM a -> RGRef<{\ x -> 1 > 0},{\ x y -> 1 > 0}> (IO ()) -> IO a @-}
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

{-@ assume forgetIOTriple :: forall <p :: RealWorld -> Prop, r :: RealWorld -> a -> Prop>.
                             IO<p,r> a -> IO a @-}
forgetIOTriple :: IO a -> IO a
forgetIOTriple a = a

{-@ atomically :: STM a -> IO a @-}
atomically :: STM a -> IO a
atomically (STM m) = do
                        r <- newRGRef (return ()) (return ()) (\ x y -> y) -- actually, rely is not reflexive
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
catchSTM (STM m) h = STM $ \ r -> do
    --old_rollback <- readIORef r
    --writeIORef r (return ())
    --r2 <- newIORef (return ())
    r2 <- newRGRef (return ()) (return ()) (\ x y -> y) -- actually, rely is not reflexive
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
                        modifyRGRef r (\ old_rollback -> (rollback_m >> old_rollback)) (\ x y -> y)
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
writeTVar (TVar ref) a = STM $ \ r -> do
    oldval <- readIORef ref
    modifyRGRef r (writeIORef ref oldval >>) (\x y -> y)
    writeIORef ref a
