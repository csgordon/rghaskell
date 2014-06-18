#!/bin/bash

PASS = true

for f in RG.hs RGTests.hs MonotonicCounter.hs;
do liquid $f;
done
