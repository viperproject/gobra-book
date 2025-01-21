# Predicates

<!-- similar to gobra tutorial -->
Predicates abstract over assertions, i.e. giving a name to a parametrized assertion.
They are suitable to denote access to recursive datastructures.
Here we define the predicate `elements` to represent access to all elements in a the list `l`:
``` go
{{#include list.go:type}}

{{#include list.go:pred}}
```
Predicates are defined with the keyword `pred` and possibly with parameters.
The body is a single self-framing assertion. <!-- only parameters as variables? -->

Note that `elements` is recursive, and represents access not only to `acc(&l.Value) && acc(&l.next)` but also to the elements in its tail.

A predicate instance is not equivalent to its body,
and we must explicitly exchange between the two with the `fold` and `unfold` statements, which we study next.


## Constructing predicates with `fold`
The `fold` statement exchanges the body of a predicate for a predicate instance.
In the following example we allocate a new list and highlight with `assert`s that the assertion from the body of `elements` holds for `l`.
With the statement `fold elements(l)` we exchange these for the predicate instance `elements(l)` as a _token_ representing access to the list.
However, `acc(&l.Value)` has been exhaled and we may no longer access `l.Value`:
``` go
{{#include list.go:fold}}
```
``` text
ERROR Assignment might fail. 
Permission to l.Value might not suffice.
```

Folding fails, if the assertion from the body does not hold:
``` go
{{#include list.go:foldfail}}
```
``` text
ERROR Fold might fail. 
Permission to elements(l.next) might not suffice.
```

We can fix this by requiring `elements(tail)` if `tail != nil`.
``` go
{{#include list.go:foldsucceed}}
```

## Unwrapping predicates with `unfold`
The `unfold` statement exchanges a predicate instance with its body.
``` go
{{#include list.go:unfold}}
```

Unfolding fails, if the predicate instance is not held.
If we try to `unfold elements(l)` twice, the second statement causes an error:
``` go
{{#include list.go:unfoldfail}}
```
``` text
ERROR Unfold might fail. 
Permission to elements(l) might not suffice.
```

## Recursive predicates
Predicates can be recursive, as seen with `elements`.
In the following example, we build a list with 3 elements, always folding the permissions.
Folding the permissions, `elements(l3)` abstracts access to the full list and has the predicate instances `elements(l2)` and `elements(l1)` folded within it.
We could continue this process, and handle a list of possibly unbounded size.
To recover the concrete permissions, we `unfold` the predicates in the reverse order.
``` go
{{#include list.go:fold3}}
```
Please note that we lose access when traversing the list to sum the elements, which is undesirable.


## Summary
> Predicates abstract over assertions, i.e. giving a name to a parametrized assertion.
>
> The `fold` statement exchanges the body of a predicate for a predicate instance. If the assertion in the body does not hold, an error is reported.
>
> The `unfold` statement exchanges a predicate instance with its body. If the predicate instance is not held, an error is reported.
