# First-class predicates

- [ ] "first-class"
  - expressions with predicate type
  - c.f. first-class functions
- [ ] predicate type
- [ ] constructor
- [ ] partial application
- [ ] equality by point-wise comparison

<!-- tutorial.md  -->
Gobra has support for first-class predicates, i.e., expressions with a predicate type.
A first-class predicate of type `pred(T1, ..., Tn)` has an arity of `n` with corresponding parameter types `T1, ..., Tn`.

To instantiate a first-class predicate, Gobra provides *predicate constructors*.
A predicate constructor `P!<d1, ..., dn!>` partially applies a declared predicate `P` with the constructor arguments `d1, ..., dn`.
A constructor argument is either a pure expression or a wildcard `_`, symbolizing that this argument of `P` remains unapplied.
In particular, the type of `P!<d1, ..., dn!>` is `pred(u1, ..., uk)`, where `u1, ..., uk` are the types of the unapplied arguments.

As an example, consider the declared predicate `pred sameValue(i1 int8, i2 uint32){ ... }`.
The predicate constructor `sameValue!<int8(1), _!>` has type `pred(uint32)`, since the first argument is applied and the second is not.
Conversely, `sameValue!<_, uint32(1)!>` has type `pred(int8)`.
Finally, `sameValue!<int8(1), uint32(1)!>` and `sameValue!< _, _!>` have types `pred()` and `pred(int8, uint32)`, respectively.

- highlight difference: assertion that access is held to a predicate instance vs an expression of predicate type

The equality operator for predicate constructors is defined as a point-wise comparison, that is, `P1!<d1, ..., dn!>` is equal to `P2!<d'1, ... , d'n!>` if and only if `P1` and `P2` are the same declared predicate and if `di == d'i` for all `i` ranging from 1 to `n`.

The body of the predicate `P!<d1, ..., dn!>` is the body of `P` with the arguments applied accordingly.
Like with other predicates, `P!<d1, ..., dn!>` can be instantiated and its instances may occur in assertions and in `fold` and `unfold` statements.
The fold statement `fold P!<d1, ..., dk!>(e1, ..., en)` exchanges the first-class predicate instance with its body. The unfold statement does the reverse.

<!-- END tutorial.md  -->
