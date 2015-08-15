#!/bin/bash
hsenv
source .hsenv/bin/activate
echo Assuming z3 is already in path
git clone https://github.com/ucsd-progsys/liquid-fixpoint.git
#git clone ssh://git@github.com/ucsd-progsys/liquid-fixpoint.git
git clone https://github.com/ucsd-progsys/liquidhaskell.git
#git clone ssh://git@github.com/ucsd-progsys/liquidhaskell.git
cd liquid-fixpoint
cabal install
cd ..
cd liquidhaskell
cabal install
cd ..
