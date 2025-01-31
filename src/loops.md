# Loops

Reasoning with loops introduces a challenge for verification.
Loops may execute an unbounded number of iterations.
As is typical in program verification, we reason about loops through [loop invariants](https://en.wikipedia.org/wiki/Loop_invariant), i.e., assertions that describe properties that hold for all iterations of the loop.

Using the example of a [binary search](./loops-binarysearch.md), we showcase how we can gradually build up the invariant until we are able to verify the function.

We will also introduce the verification of loops with [`range`](./loops-range.md) clauses.

[Termination](./termination.md) of loops will be discussed in a following section.
