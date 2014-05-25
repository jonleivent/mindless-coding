
mindless-coding
===============

Mindless, Verified (Erasably) Coding using Dependent Types

This project demonstrates:

1. How "fully-specified" coding using dependent types can actually
simplify the task of implementing complex algorithms, while providing
full verification of the resulting (extracted) code.

2. How to cause all proof-related parts to be erased in the resulting
extracted code, such that the extracted code is very human readable
and does not carry any extra runtime burden from its verification.  As
was pointed out by others, the erasability mechanism used here is very
similar to one described in:

http://www.pps.univ-paris-diderot.fr/~letouzey/download/Letouzey_Spitters_05.pdf

3. How tactics, automation, and interaction with the proof assistant
can further simplify the task of implementing complex algorithms.

Points 1 and 3 combined are what the term "mindless coding" refers to.
Fully-specified dependently typed structures (avltree and rbtree) and
their functions (find, insert, delmin and delete) not only produce
fully verified results - they also reduce the task of function
implementation to a stepwise refinement of intermediate steps (proof
subgoals) that are constrained to the point where the programmer
(prover) is freed from consideration of the overall algorithm involved
during each step.  In many cases, the steps are fully automatable.  In
others, the information provided by the subgoal's context, along with
a "rough idea" of what the algorithm being implemented should do, is
usually sufficient for the programmer to make progress to the next
subgoal.

Perhaps the best illustration of this "mindless" point is the
implementation of the complex rebalancing functions for Red/Black
trees, which are widely viewed as difficult to do correctly.  These
were implemented using this "mindless-coding" technique without
relying on any outside explanatory material or implementations.  The
modularization of the implementations into separate functions was done
after-the-fact just as a way to make the resulting proofs and
extracted code easier to read.

The goal of the project is to develop (mindless-coding) techniques
that programmers inexperienced with theorem proving can use to
generate correct programs, where these techniques are potentially
easier to use than standard programming languages and ad-hoc software
engineering practices.  Hopefully, this will help transfer the
technology of dependent types and theorem proving to a much wider
audience.

So far, this demonstration includes two examples: AVL trees (Coq
source: avl.v, extracted OCaml: avl.ml and avl.mli) and Red/Black
trees (Coq source: redblack.v, extracted OCaml: redblack.ml and
redblack.mli).

FAQ:

- What is meant by "fully-specified"?  Specifications, such as the
  dependently-typed inductive definitions of avltree and rbtree, and
  the dependently-typed arguments and results of their functions, are
  made sufficiently complete so as to constrain any implementation
  that type-checks to be fully correct.  For example, the avltree and
  rbtree types both include a contents index that constrains each tree
  to contain exactly the specified contents in exactly the specified
  (sorted) order.  Performance-related properties are not included -
  but this might be pursued in the future.

- Why is "fully-specified" important?  Highly constraining
  specifications, in the form of very proof-laden dependent types, can
  guide the implementation to the point where the programmer only
  needs to be concerned with satisfying small incremental goals,
  (mostly) without carrying around the cognitive load of the
  algorithm's details.

- Why Coq, why not Agda or Idris?  Coq's Prop universe is almost a
  fully functional erasability mechanism as is - it just needs a
  single injectivity axiom on a single Prop (Erasable) to be fully
  functional.  As far as I can tell, something similar isn't possible
  with Agda's irrelevance notations because they already incorporate
  proof irrelevance (whereas in Coq, proof irrelevance is an optional
  additional axiom that isn't - and can't be - used here).  Idris is
  expected to eventually have its own built-in erasability mechanism,
  but doesn't at this time.

- Why program using proofs?  Functions are implemented in Coq using
  tactics in proof mode for three reasons: to benefit from the
  interactive-ness of proof mode, to enable the usage of tactics and
  proof-search automation, and to avoid the complexity behind
  successful use (the "convoy pattern") of the match-with construct in
  Coq in the presence of dependent types with complex indices.  If
  development was done in Idris instead of Coq, it might be possible
  to interleave tactic and expression based methods together to
  achieve a similar result.

- Why is erasability important?  Erasability is important because it
  eliminates the concern that fully-constrained specifications would
  burden executable code with the proof-related paraphernalia.

- Why explicit erasability?  Why not allow the compiler to do it all
  for you?  This is an on-going debate.  Note that there is nothing
  about this demonstration that requires that the compiler not find
  more to erase, and erase it.  The opinion of the author is that
  having erasability work as a type constraint during implementation
  of functions helps to prevent the programmer from accidentally
  "cheating" by raiding should-be-erased code and using some
  information obtained from it in run-time (unerased) code, thus
  destroying the erasable-ness of the former.  There is a similar
  effect on tactics - they can't cheat either, so a more liberal usage
  of tactics and automation is not discouraged.  One point of the
  demonstration here is that explicit erasability doesn't imply messy
  development - for example, it doesn't require re-implementation of
  any existing types or functions.

- Why AVL nd Red/Black trees?  They are well known, useful, and
  (especially in the case of Red/Black trees) difficult to get right.
  Hence, the ability here to "mindlessly" implement the find, insert,
  delmin, delete and respective rebalancing functions with full
  erasability of all proof-related paraphernalia, yet with
  simple-to-read proofs, is a non-trivial accomplishment.
