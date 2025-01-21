# Abstraction and Information Hiding

<!-- simple explanation, without "give a name to a parameterised assertion"(viper) -->
<!-- abstract over an assertion  (another abstract...) -->
In this chapter, we introduce _predicates_.
Predicates can be used for representing memory access to data structures of possibly unbounded size, such as linked lists or binary trees and to achieve [information hiding](https://en.wikipedia.org/wiki/Information_hiding).
We will abstract memory access to a data structure with predicates that hide implementation details,
such as non-exported fields, memory layout, or any other internal assumptions.
<!-- designing APIs that do not leak private information -->

<!-- that could be confusing, needs an example? -->
Through an _abstraction function_ we map structures to their essential representation.
For this we often use _mathematical types_, a kind of ghost types.
<!-- sounds like we can't otherwise? -->
With the abstracted representation we can specify functional correctness requirements.
For example, if we were to design a `Set` data structure, adding an element to a concrete `Set` shall have the same effect as the operation on an abstract, mathematical set.


## Running example: linked list
Throughout the sections of this chapter we will follow the example of a `List` data structure for storing integer values,
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

// Get returns the element at index i in the list
func (l *List) Get(i int) (value int)

// Returns true iff the list is empty.
func (l *List) IsEmpty() (empty bool) {

// Returns the length of the list.
func (l *List) Length() (length int)
```

<!-- TODO client example -->
``` go
ll := Empty()
l0 := ll.Length()
//@ assert l0 == 0
ll = New(11, ll)
//@ assert ll.Head() == 11
l1 := ll.Length()
//@ assert l1 == 1
ll = ll.Tail()
ll = New(22, Empty())
//@ assert ll.Head() == 22
ll = New(33, ll)
//@ assert ll.Head() == 33
l2 := ll.Length()
//@ assert l2 == 2
v0 := ll.Get(0)
v1 := ll.Get(1)
//@ assert v0 == 33
//@ assert v1 == 22
ll := ll.Remove(1)
l3 := ll.Length()
//@ assert ll.Head() == 33
//@ assert l3 == 1
```


In a first step, we focus only on specifying memory access.
Then in the second step, the contracts are completed for functional correctness.


[^1]: Go's standard library comes with a [doubly linked list](https://pkg.go.dev/container/list).
While it has been verified ([Verifying Go’s Standard Library (Jenny)](https://ethz.ch/content/dam/ethz/special-interest/infk/chair-program-method/pm/documents/Education/Theses/Adrian_Jenny_PW_Report.pdf)), we use a much simpler API for our exposition.
