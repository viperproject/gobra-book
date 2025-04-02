# Abstraction functions

An idiomatic verification pattern is to map structures to their essential representation with an _abstraction function_. 
One way to specify functional correctness is by describing the effect of functions or methods on the abstract representation.
For the abstract representation, we use _mathematical types_, i.e., ghost types representing mathematical objects, such as sequences or sets.
For example, if we were to design a `Set` data structure, adding an element to a concrete `Set` shall have the same effect as the operation on an abstract, mathematical set.

## Abstraction function for `List`
So far, our contracts for `List` were concerned with memory access.
Now, we want to complete them with functional correctness requirements.

The essence of a `List` is captured by a sequence.
We will not fully introduce sequences at this point, but refer the reader to the [mathematical types reference](../reference-mathematical-types.md) if questions arise.

A sequence of integers `seq[int]` is constructed recursively from the list, concatenating (`++`) the sequences.
By convention, the abstraction function is called `View`.
Note that the function must be `pure`, as we want to use it in specifications.
``` go verifies
{{#include list.go:view}}
```


## Functional correctness for `List` 
For the methods of the `List` API, we can specify their functional behavior on the abstract object.
For example, `New` corresponds to the concatenation of a single element to a sequence.

In the table, we give the preconditions and postconditions we add to the contracts.
The abstraction function is heap dependent, and we can evaluate it in the `old` state to get the original representation.
For example, the method `Get` must return the `i`th element of the sequence corresponding to the list `old(l.View()[i])` index the index is within bounds ( `0 <= i && i < len(l.View())`).
<!-- TODO heap dependent (there is no heap in Go spec!) -->

| name      | `requires`                    | `ensures`                                                          |
|-----------|-------------------------------|--------------------------------------------------------------------|
| `New`     |                               | `out.View() == seq[int]{value} ++ old(tail.View())`                |
| `Tail`    |                               | `out.View() == old(l.View()[1:])`                                  |
| `Remove`  | `0 <= i && i < len(l.View())` | `out.View() == old(l.View()[:i] ++ l.View()[i+1:])`                |
| `Head`    |                               | `value == l.View()[0]`                                             |
| `Get`     | `0 <= i && i < len(l.View())` | `value == l.View()[i]`                                        |
| `IsEmpty` |                               | `empty == (len(l.View()) == 0)` |
| `Length`  |                               | `length == len(l.View())`                                                                   |

<!-- framing, when because of fractional must not say that sequence stays the same -->

The full example can be found here: [full linked list example](./full-example.md).
