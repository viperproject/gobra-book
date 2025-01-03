# Loops

Reasoning with loops introduces a challenge for verification.
Loops could execute an unbounded number of iterations.
Similar to pre and postconditions for functions, we have to write a specification for a loop in the form of  [invariants](./loops-invariant.md).

Using the example of a [binary search](./loops-binarysearch.md), we showcase how we can gradually build up the invariant until we are able to verify the function.

We will also introduce the verification of loops over [`range`](./loops-range.md) clauses.

[Termination](./termination.md) of loops will be discussed in a following section.
