# Summary

[Overview](./overview.md)

# The basics
- [Introduction]()
- [Installation]()
<!-- - [Getting started]() -->
- [Basic specifications](./01/basic-specs.md)
  <!-- - [`assert` and `assume`](./assert-assume.md) -->
  <!-- - [requires, ensures, and preserves](./requires-ensures.md)-->
- [Verifying programs with arrays](./01/basic-array.md)
- [Quantifiers (`forall`, `exists`) and Implication (`==>`)](./01/quantifier.md)
- [Loops](./01/loops.md)
  - [Loop Invariants](./01/loops-invariant.md)
  - [Binary Search](./01/loops-binarysearch.md)
  - [Range](./01/loops-range.md)
- [Overflow Checking](./01/overflow.md)
- [Termination](./01/termination.md)
- [Ghost code](./01/ghost.md)
- [Pure functions](./01/pure.md)

# Reasoning about Memory Accesses with Permissions
- [Permission to write](./02/permission-write.md)
- [Self-framing assertions](./02/self-framing.md)
- [Addressability, `@` and sharing](./02/addressable.md)
- [Permission to read](./02/fractional-permissions.md)
  - [Wildcard permission](./02/wildcard-permission.md)
  - [Permission type and parameters](./02/permission-type.md)
- [Inhaling and exhaling](./02/inhale-exhale.md)
- [Quantified permissions](./02/quantified-permission.md)
- [Pure functions and permissions](./02/permission-pure.md)
- [Slices](./02/slices.md)
- [Maps](./02/maps.md)
- [Variadic functions]()

# Abstraction and Information Hiding
- [Predicates, `fold`, and `unfold`](./03/predicates.md)
- [Abstracting memory access with predicates](./03/abstracting-memory.md)
- [`unfolding` predicates](./03/unfolding.md)
- [Predicates and fractional permissions](./03/predicates-fractional.md)
- [Abstraction functions](./03/abstraction-view.md)
- [Predicates as termination measures](./03/predicate-termination.md)
- [Full linked list example](./03/full-example.md)

# Interfaces
- [Behavioral subtypes](./04/behavioral.md)
- [`nil` interface values](./04/nil.md)
- [Type assertions, `typeOf`](./04/type.md)
- [Abstracting memory with predicate interface members](./04/mem.md)
- [Implementation proofs (`implements`)](./04/implements.md)
- [Case study: `sort.Interface`](./04/sort.md)
- [Interfaces and termination](./04/interface-termination.md)
- [Comparable interfaces, `isComparable`](./04/comparable.md)
- [The `error` interface]()
- [Full example: `image`](./04/image.md)

# Concurrency
- [Goroutines and data races](./05/goroutine.md)
- [First-class predicates](./05/first-class-predicates.md)
- [Reasoning about mutual exclusion with `sync.Mutex`](./05/mutex.md)
- [`defer` statements](./05/defer.md)
- [Share memory by communicating over channels]()
- [Waiting on goroutines with `sync.WaitGroup`]()

# Advanced topics
- [Quantifier Triggers](./triggers.md)
- [Magic Wands](./magic-wands.md)

---
- [Mathematical types](./reference-mathematical-types.md)
- [Playground](./playground.md)
