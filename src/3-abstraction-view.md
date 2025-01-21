# Abstraction functions

So far, our contracts were concerned with memory access.
Now we want to complete them with functional correctness.
To specify functional correctness, we provide a mapping from our Go types to a mathematical object.

The essence of a `List` is captured by sequence.
We will not fully introduce sequences at this point, but refer the reader to the [mathematical types reference](./referece-mathematical-types.md) if questions arise.

<!-- convention to call View -->

## Abstraction function `View`
A sequence of integers `seq[int]` is constructed recursively from the list, concatenating (`++`) the sequences.
``` gobra
{{#include list.go:view}}
```

<!-- TODO heap dependent -->

## Functional correctness for `List` 
For the methods of the `List` API, we can specify their functional behavior on the abstract object.
E.g. `New` corresponds to the concatenation of a single element to a sequence.

In the table, we give the preconditions and postconditions we add to the contracts:

| name      | `requires`                    | `ensures`                                                          |
|-----------|-------------------------------|--------------------------------------------------------------------|
| `New`     |                               | `out.View() == seq[int]{value} ++ old(tail.View())`                |
| `Tail`    |                               | `out.View() == old(l.View()[1:])`                                  |
| `Remove`  | `0 <= i && i < len(l.View())` | `out.View() == old(l.View()[:i] ++ l.View()[i+1:])`                |
| `Head`    |                               | `value == l.View()[0]`                                             |
| `Get`     | `0 <= i && i < len(l.View())` | `value == old(l.View()[i])`                                        |
| `IsEmpty` |                               | `(!empty ==> len(l.View()) > 0) && (empty ==> len(l.View()) == 0)` |
| `Length`  |                               | `length == len(l.View())`                                                                   |

<!-- TODO framing, when because of fractional must not say that sequence stays the same -->

The full example can be found here: [full linked list example](./3-full-example.md).
