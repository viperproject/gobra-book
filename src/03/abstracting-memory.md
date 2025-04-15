# Abstracting memory access with predicates

In this section, we emphasize how predicates can abstract memory access and help enforce the [information hiding](https://en.wikipedia.org/wiki/Information_hiding) principle,
hiding implementation details such as non-exported fields, memory layout, or other internal assumptions.

The core idea is that clients only need to hold predicate instances, allowing them to interact with an API without exposing specific permissions to fields.
We exemplify this on a subset of the `List` API, focusing only on specifying memory access without proving functional correctness for now.

Previously, we defined the predicate `elements`:
``` go
{{#include list.go:pred}}
```

Predicates can be defined with a receiver, too.
This conveniently couples the predicate to the type.
As a convention, we choose the name `Mem` to signal that this predicate abstracts the memory.
``` go
{{#include list.go:type}}
{{#include listMem.go:mem}}
```
Note the slight difference: for `l.Mem()`, `l` could be `nil` whereas `elements(l)` implies `l != nil`.
<!-- We will shortly explain this decision. -->


A predicate instance `l.Mem()` can be obtained, for example, by allocating a new list.
The postconditions of `Empty` and `New` ensure this.
For `New`, the contract, in turn, requires holding `tail.Mem()`.
``` go verifies
{{#include listMem.go:empty}}
{{#include listMem.go:new}}
```

Let us put this in contrast with the function `NewBad`:
``` go
{{#include listMem.go:newbad}}
```
The contract is bad in several ways:
- The field `next` is used in the contract, although it is non-exported, and the package's clients are unaware of its existence.
- Internal decisions are leaked, such as using a linked list to provide the `List` API.
- When the implementation is changed, the contract also needs to get changed, breaking the API.

## Hiding implementation details
Another internal decision is the encoding of the empty list.
In this example, we implement it as `(*List)(nil)`.
While this is an idiomatic choice in Go, we still exemplify how this can be hidden.
Some functions like `Head` cannot be called with an empty list.
The precondition `l != nil` would leak this to clients.
Instead, we provide a `pure` method `IsEmpty` to be used in contracts.
``` go verifies
{{#include listMem.go:empty}}
{{#include listMem.go:isempty}}
{{#include listMem.go:head}}
{{#include listMem.go:client}}
```

Note that we implement `Mem` so that it also holds for the empty list.
This enables us to call methods such as `e.IsEmpty()` on it.


## List example so far
``` go
{{#include listMem.go:all}}
```
