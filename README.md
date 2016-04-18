RG-Haskell: Liquid Rely-Guarantee References
=============================================

This is an embedding of a slightly simplified *rely-guarantee reference* system into
[Liquid Haskell](https://github.com/ucsd-progsys/liquidhaskell/).
(See "[Rely-Guarantee References for Refinement Types over Aliased Mutable Data](http://dl.acm.org/citation.cfm?id=2462160),"
by [Gordon](http://homes.cs.washington.edu/~csgordon/), [Ernst](http://homes.cs.washington.edu/~mernst/), and [Grossman](http://homes.cs.washington.edu/~djg/), PLDI'13.  I promise to never use such a long paper
title ever again.)  It also includes concurrency extensions from [Verifying Concurrent Programs by
Controlling Alias Interference](https://dlib.lib.washington.edu/researchworks/handle/1773/26020).

The key idea is to augment each reference with a predicate refining
the referent and heap reachable from it, and binary relations describing permitted
local actions (the guarantee) and possible remote actions (the rely):

             ref{T|P}[R,G]

The terminology comes from rely-guarantee reasoning, from the concurrent program
logic literature.  As long as
each reference's guarantee relation is a subrelation of any alias's rely (plus some
subtle side conditions about nested references), any predicate P that is /stable/
with respect to a rely R on a given reference (forall x y, P x -> R x y -> P y)
is trivially preserved by any update through an alias that respects that alias's
guarantee relation.

Embedding into Liquid Haskell instead of Coq requires a few weakenings of the
original design, so we lose expressiveness but gain substantially from automation
and being a refinement of a language with real programs!  The main simplifications are:
 - We must always have that the guarantee implies the rely, since Haskell wouldn't
   respect the substructural restrictions.
 - Predicates and relations can refer only to the immediate referent for now.
 - Folding (pushing a local restriction through to new references reached via
   dereference) doesn't exist in this system, mostly because all predicates and
   relations can restrict only one cell.


Dependencies
------------
At some point there was some history rewriting in the liquid-fixpoint and liquidhaskell
repositories; it looks like the old external dependencies that had been checked in (OCaml
dependencies) had been purged from the repository, which both changes all the git hashes and breaks
checkouts of older commits.

Currently you should use the HEAD of the following repositories:
- [csgordon/liquid-fixpoint-snapshot](https://github.com/csgordon/liquid-fixpoint-snapshot) as a
  pre-rewriting stand-in for ucsd-progsys/liquid-fixpoint
- [csgordon/liquidhaskell-snapshot](https://github.com/csgordon/liquidhaskell-snapshot) as a
  pre-rewriting stand-in for ucsd-progsys/liquidhaskell

See also the VM image linked from the main [rely-guarantee references
page](https://csgordon.github.io/rgref).
