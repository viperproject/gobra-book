# Case study: `sort.Interface`

> TODO
> This section might change.
> To specify a sort algorithm we might have to change the specs for `View` and the requirements for `Less`.

In this section, we deepen the concepts introduced in the previous sections on interfaces with a larger example from the Go standard library.

The interface `Interface` is used for various sorting routines in the [sort package](https://pkg.go.dev/sort).
This interface describes a collection with a length, where elements can be compared and swapped.

<!-- abstracting over different types and orders -->

As usual, we define a `Mem` predicate to abstract memory access to the collection.
We extend the interface with a `View` method abstracting the collection to a sequence, such that we can specify the methods in terms of their effect on the abstracted data type.
``` go
{{#include ./sort.go:Interface}}
```
A pure and ghost analogue, `LessSpec`, of the `Less` method is defined so that we can use it in specifications.
To couple them together, the result of calling `Less` is equivalent to the result of calling `LessSpec` in that state (`res == old(LessSpec(i, j))`).


Using the abstraction `View`, we can specify what it means to swap the elements with indices `i` and `j` as:
``` go
{{#include ./sort.go:InterfaceSwap}}
```
Note we use the [sequence update](../reference-mathematical-types.md) operation to create the sequence `oldView[i = oldj][j = oldi]` where we exchange two elements.
Also, we use the binding `let v := e1 in e2` to assign the expression `e1` to the variable `v` in the expression `e2`.


The `ghost` methods `LessIsConnected` and `LessIsTransitive` formalize the requirements described in the docstring:
``` go
{{#include ./sort.go:LessDoc}}
```
To implement the interface, one must implement these ghost methods, or equivalently prove the lemmas that the ordering is [connected](https://en.wikipedia.org/wiki/Connected_relation) and transitive.

``` go
{{#include ./sort.go:InterfaceLessIsConnected}}

{{#include ./sort.go:InterfaceLessIsTransitive}}
```

Note that in the postcondition of `LessIsConnected` we compare the sequence elements using the ghost comparison `===` which compares values of arbitrary types by identity.
If we used the normal equality `==` instead, Gobra reports an error since the sequence contains elements of type `any` which might not be directly comparable.
``` go
// ...
// @ ensures let view := old(View()) in view[i] == view[j]
```
``` text
ERROR Comparison might panic. 
Both operands of view[i] == view[j] might not have comparable values.
```


Having specified the interface, we can specify and verify other functions from the `sort` package, such as
[IsSorted](https://cs.opensource.google/go/go/+/refs/tags/go1.24.0:src/sort/sort.go;l=108).
Previously, we have seen similar functions for concrete types, such as integer arrays or slices.
Now we have a function that works for any type implementing `Interface`.
``` go
{{#include ./sort.go:IsSorted}}
```
  
## Example implementation: `IntSlice`
As an example, we implement `Interface` for integer slices.
``` go
{{#include ./sort.go:IntSliceType}}
```
The `Mem` predicate simply wraps access to the slice.
``` go
{{#include ./sort.go:IntSliceMem}}
```

We define `Less` as `s[i] < s[j]`.
For integers, this order is clearly transitive (`s[i] < s[j]` and `s[j] < [k]` implies `s[i] < [k]`)
and connected (`!(s[i] < s[j])` and `!(s[j] < s[i])` implies `s[i] == s[j]`).
No proof annotations are required for this.
``` go
{{#include ./sort.go:IntSliceLess}}

```

The abstraction function `View` converts the slice to a sequence.
With the helper function `viewAux` we recursively construct the sequence while building up the postcondition that we have already converted the current prefix.
<!-- - (must use unfolding there) -->
``` go
{{#include ./sort.go:IntSliceView}}
```

`Len` and `Swap` are implemented straightforwardly as the corresponding operations on the `IntSlice`.
We only have to add `fold` and `unfold` statements to convert between the `Mem` predicate and the permissions to the slice.
``` go
{{#include ./sort.go:IntSliceLen}}
```
``` go
{{#include ./sort.go:IntSliceSwap}}
```

As the contracts of the implementation methods match the contracts of the interface methods we do not have to give an implementation proof.
``` go
{{#include ./sort.go:IntSliceImplements}}
```

Having implemented `Interface`, we may now call `IsSorted(x)` with `IntSlice` values:
``` go
{{#include ./sort.go:client}}
```

## Quiz
{{#quiz ../../quizzes/sort-interface.toml}}

## Full example

``` go
{{#include ./sort.go:all}}
```
