# First-class predicates
<!-- Based on tutorial.md  -->
Gobra has support for first-class predicates, i.e., expressions with a predicate type.
A first-class predicate of type `pred(T1, ..., Tn)` has arity `n` with corresponding parameter types `T1, ..., Tn`.

This section serves as a prerequisite for the next section where we associate a predicate as the invariant of a lock.
First-class predicates enables us to use predicates as parameters or return values of functions or methods.

## Predicate constructors `P!<...!>`
To instantiate a first-class predicate, Gobra provides _predicate constructors_.
A predicate constructor `P!<d1, ..., dn!>` partially applies a declared predicate `P` with the constructor arguments `d1, ..., dn`.
A constructor argument is either a pure expression or a wildcard `_`, indicating that this argument of `P` remains unapplied.
In particular, the type of `P!<d1, ..., dn!>` is `pred(u1, ..., uk)`, where `u1, ..., uk` are the types of the unapplied arguments.

For example, consider the declared predicate `Mem`:
``` go
{{#include ./first-class-predicates.go:Pred}}
```
The predicate constructor `Mem!<new(int8), _!>` has type `pred(*uint32)`, since the first argument is applied and the second is not.
Conversely, `Mem!<_, new(uint32)!>` has type `pred(*int8)`.
Finally, `Mem!<new(int8), new(uint32)!>` and `Mem!< _, _!>` have types `pred()` and `pred(*int8, *uint32)`, respectively.

 <!-- (for `x *int8` and `y *uint32`) -->
Note the differences:
- `Mem(x, y)` is an assertion. Short for `acc(Mem(x, y), 1)`, stating that access is held to this predicate instance.
- `Mem!<x, y!>` is a predicate constructor, an expression of type `pred()`.
- `Mem!<x, y!>()` is again an assertion, stating that access is held for this first-class predicate instance.


## Equality of first-class predicates

The equality operator for predicate constructors is defined as a point-wise comparison, that is, `P1!<d1, ..., dn!>` is equal to `P2!<d'1, ..., d'n!>` if and only if `P1` and `P2` are the same declared predicate and if `di == d'i` for all `i` ranging from 1 to `n`.

For example, the `Mem` predicate constructor is equal if all applied arguments are equal.
But it is not equal to a different declared predicate such as `OtherMem`.
``` go
{{#include ./first-class-predicates.go:Eq}}
{{#include ./first-class-predicates.go:Pred2}}
```
``` text
ERROR Assert might fail.
Assertion OtherMem!<a, c!> == Mem!<a, c!> might not hold.
```

## `fold` and `unfold` first-class predicates
The body of the predicate `P!<d1, ..., dn!>` is the body of `P` with the arguments applied accordingly.
Like with other [predicates](../03/predicates.md), the first-class predicate `P!<d1, ..., dn!>` can be instantiated and its instances may occur in assertions and in `fold` and `unfold` statements.
The `fold` statement `fold P!<d1, ..., dk!>(e1, ..., en)` exchanges the first-class predicate instance with its body.
The `unfold` statement does the reverse.

In the following example, we fold and unfold a first-class predicate instance as opposed a normal predicate instance `Mem(x, y)`.
``` go
{{#include ./first-class-predicates.go:fold}}
```
