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
- [Permission to write](./permission-write.md)
- [Self-framing assertions](./self-framing.md)
- [Addressability, `@` and sharing](./addressable.md)
- [Permission to read](./fractional-permissions.md)
  - [Wildcard permission](./wildcard-permission.md)
  - [Permission type and parameters](./permission-type.md)
- [Inhaling and exhaling](./inhale-exhale.md)
- [Quantified permissions](./quantified-permission.md)
- [Pure functions and permissions](./permission-pure.md)
- [Slices](./slices.md)
- [Maps](./maps.md)
- [Variadic functions]()

# Abstraction and Information Hiding
- [Predicates, `fold`, and `unfold`](./3-predicates.md)
- [Abstracting memory access with predicates](./3-abstracting-memory.md)
- [`unfolding` predicates](./3-unfolding.md)
- [Predicates and fractional permissions](./3-predicates-fractional.md)
- [Abstraction functions](./3-abstraction-view.md)
- [Predicates as termination measures](./3-predicate-termination.md)
- [Full linked list example](./3-full-example.md)
- [Abstract predicates]()

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

# Advanced topics
- [Quantifier Triggers](./triggers.md)
- [Magic Wands](./magic-wands.md)

---
- [Mathematical types](./reference-mathematical-types.md)
