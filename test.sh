#!/bin/bash

# STMLog example is broken due to LH regression
for f in RG.hs \
         RGTests.hs \
         examples/MonotonicCounter.hs \
         examples/LockfreeMonotonicCounter.hs \
         examples/MonotonicCounterClient.hs \
         examples/CASList.hs \
         examples/HellerSet.hs \
         examples/HellerSetClient.hs;
do 
liquid $f --no-prune-unsorted &> /dev/null;
RET="$?"
if [ "$RET" -eq "0" ];
then
    echo $f: PASS;
elif [ "$RET" -eq "1" ];
then
    echo $f: WARNING, nontermination or inference of false
else
    echo $f: FAIL;
fi
done
