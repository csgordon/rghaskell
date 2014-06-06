Using Liquid Haskell with Cabal
-------------------------------
To use LH with Cabal builds:

0. Create a script named 'ghc' on your path, which executes: 'liquid -q --ghcoptions $@ -i/opt/liquid'.  This passes expected options through LH.
1. Download the source for the package in question.
2. Run 'cabal configure' in a normal terminal environment (LH spits out a copyright statement that confuses the normal GHC version check)
3. Add to text.cabal, under the 'library' heading: 'hs-source-dirs: . <path-to-RG.hs>' (this adds the RG module to the search path)
4. In a shell configured to run the 'liquid' executable, run 'cabal build'
