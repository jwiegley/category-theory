# Category Solver

There are some equivalences in category-theory that are very easily expressed
and proven, but slow to establish in Coq using only symbolic term rewriting.
For example:

    (f ∘ g) △ (h ∘ i) ≈ split f h ∘ g △ i

This is solved by unfolding the definition of split, and then rewriting so
that the fork operation (here given by `△`) absorbs the terms to its left,
followed by observing the associativity of composition, and then simplify
based on the universal properties of products. This is repeated several times
until the prove is trivially completed.

Although this is easy to state, and even to write a tactic for, it can be
extremely slow, especially when the types of the terms involved becomes large.
A single rewrite can take several seconds to complete for some terms, in my
experience.

The goal of this solver is to reify the above equivalence in terms of its
fundamental operations, and then, using what we know about the laws of
category theory, to compute the equivalence down to an equation on indices
between the reduced terms. This is called *computational reflection*, and
encodes the fact that our solution only depends on the categorical structure
of the terms, and not their type.

That is, an incorrectly-built structure will simply fail to solve; but since
we're reflecting over well-typed expressions to build the structure we pass to
the solver, combined with a proof of soundness for that solver, we can know
that solvable, well-typed, terms always give correct solutions. In this way,
we transfer the problem to a domain without types, only indices, solve the
structural problem there, and then bring the solution back to the domain of
full types by way of the soundness proof.
