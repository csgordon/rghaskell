#!/bin/bash

for f in RG.hs RGTests.hs examples/MonotonicCounter.hs examples/LockfreeMonotonicCounter.hs examples/STMLog.hs examples/CASList.hs;
do 
liquid $f &> /dev/null;
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
