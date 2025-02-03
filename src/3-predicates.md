# Predicates

<!-- similar to gobra tutorial -->
Predicates abstract over assertions, i.e., giving a name to a parametrized assertion.
Predicates can be used for representing memory access to data structures of possibly unbounded size, such as linked lists or binary trees.
While quantified permissions are often used to specify pointwise access, e.g. to elements of a slice, predicates are suitable to denote access to recursive data structures.

## Running example: `List`
Throughout the sections of this chapter, we will follow the example of a `List` data structure for storing integer values,
implemented as a singly linked list[^1].

``` go
{{#include list.go:type}}
```

We will implement the following public API for the construction and manipulation of lists:
``` go
// Returns the empty list.
func Empty() (l *List)

// New creates a new List node with the specified value and tail.
func New(value int, tail *List) (out *List)

// Tail returns a new list that is the tail of the original list,
// excluding the first element.
func (l *List) Tail() (out *List)

// Remove returns the list with the element at index i deleted.
func (l *List) Remove(i int) (out *List)

// Head returns the value of the first element in the list.
func (l *List) Head() (value int)

// Get returns the element at index i in the list.
func (l *List) Get(i int) (value int)

// Returns true iff the list is empty.
func (l *List) IsEmpty() (empty bool) {

// Returns the length of the list.
func (l *List) Length() (length int)
```

In a first step, we focus only on specifying memory access.
Then in the second step, the contracts are completed for functional correctness.
The following client code will be verified in the final example:
``` go
{{#include list.go:client}}
```


## Defining predicates
Here we define the predicate `elements` to represent access to all elements in a list `l`:
``` go
{{#include list.go:type}}

{{#include list.go:pred}}
```
Predicates are defined with the keyword `pred` and possibly with parameters.
The body is a single self-framing assertion. <!-- only parameters as variables? -->

Note that `elements` is recursive, and represents access not only to `acc(&l.Value) && acc(&l.next)`, but also to the elements in its tail.

A predicate instance is not equivalent to its body
and we must explicitly exchange between the two with the `fold` and `unfold` statements, which we study next.


## Constructing predicates with `fold`
The `fold` statement exchanges the body of a predicate for a predicate instance.
In the following example we allocate a new list and highlight with `assert`s that the assertion from the body of `elements` holds for `l`.
With the statement `fold elements(l)` we exchange these for the predicate instance `elements(l)` as a token representing access to the list.
However, `acc(&l.Value)` has been exhaled and we may no longer access `l.Value`:
``` go
{{#include list.go:fold}}
```
``` text
ERROR Assignment might fail. 
Permission to l.Value might not suffice.
```

Folding fails if the assertion from the body does not hold:
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
`elements(l3)` abstracts access to the full list and has the predicate instances `elements(l2)` and `elements(l1)` folded within it.
We could continue this process, and handle a list of possibly unbounded size.
To recover the concrete permissions, we `unfold` the predicates in the reverse order.
``` go
{{#include list.go:fold3}}
```
Please note that we lose access when traversing the list to sum the elements, which is undesirable.


## Summary
> Predicates abstract over assertions, i.e., giving a name to a parametrized assertion.
>
> The `fold` statement exchanges the body of a predicate for a predicate instance. If the assertion in the body does not hold, an error is reported.
>
> The `unfold` statement exchanges a predicate instance with its body. If the predicate instance is not held, an error is reported.


[^1]: Go's standard library comes with a [doubly linked list](https://pkg.go.dev/container/list).
While it has been verified ([Verifying Go’s Standard Library (Jenny)](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Adrian_Jenny_PW_Report.pdf)), we use a much simpler API for our exposition.
