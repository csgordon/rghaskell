#!/bin/bash

for f in RG.hs RGTests.hs examples/MonotonicCounter.hs examples/LockfreeMonotonicCounter.hs examples/STMLog.hs examples/CASList.hs;
do 
liquid $f &> /dev/null;
if [ "$?" -eq "0" ];
then
    echo $f: PASS;
elif [ "$?" -eq "1" ];
then
    echo $f: WARNING, nontermination or false
else
    echo $f: FAIL;
fi
done
