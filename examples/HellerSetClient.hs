module HellerSetClient where

import RG
import HellerSet

-- This client looks a lot like the monotonic counter's client.  But there the use of
-- RGRefs ensures that a dynamic assertion always passes, while here RGRefs are 
-- enforcing something slightly more subtle: the representation invariant of the set
-- (that the underlying list remains sorted).  Without the guarantees from RGRefs, the
-- other code could reorder elements or insert large elements at the front of the list,
-- and the find on the last line would return early without finding a still-reachable
-- 3.  With the invariants enforced by RGRefs, the final find will return false only if the other
-- code actually removed 3 from the set --- while preserving the sortedness invariant.

{-@ client :: (SetHandle Int -> IO ()) -> IO Bool @-}
client :: (SetHandle Int -> IO ()) -> IO Bool
client other = do { s <- newSet;
                    insert s 3;
                    insert s 4;
                    other s;
                    find s 3
                  }
