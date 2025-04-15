# Comparable interfaces, `isComparable`

Comparing two interfaces may cause a runtime error if both dynamic values are incomparable.
For example, slices are not comparable in Go:
``` go panics
{{#include comparable.go:main}}
```
``` text
panic: runtime error: comparing uncomparable type []int

goroutine 1 [running]:
main.main()
	/home/gobra/comparable.go:52 +0x77
exit status 2
```

Gobra provides the function `isComparable`, which takes an interface value or a type as input and returns whether it is comparable according to Go.
When an implementation's value is stored in an interface value, Gobra records whether the resulting interface value is comparable.
In the following example, we assign the numeric constant `5` to `x`, which makes it comparable.

``` go verifies
{{#include comparable.go:isComparable}}
```

As an example, we change the linked [`List`](../03/full-example.md) type to store values of type `any` (which is a shorthand for the empty interface `interface{}`).
``` go
{{#include comparable.go:type}}
```
Note that we can store arbitrary values in the list, as every type trivially implements the empty interface.

The recursive function `Contains` that searches the list for a `value` might panic because of the comparison `l.Value == value` between possibly incomparable values, which Gobra detects:
``` go does_not_verify
// @ requires acc(l.Mem(), 1/2)
// @ pure
// @ decreases l.Mem()
{{#include comparable.go:Contains1}}
```
``` text
ERROR Comparison might panic.
 Both operands of l.Value == value might not have comparable values.
```

We define the function `Comparable` to require that the `List` contains only comparable elements.
With `isComparable`, we state recursively that each element must be comparable.
``` go
{{#include comparable.go:Comparable}}

{{#include comparable.go:Contains}}
```

The following client code verifies.
``` go verifies
{{#include comparable.go:client}}
```

> Comparing two interfaces may cause a runtime error if both dynamic values are incomparable.
> 
> The function `isComparable` takes an interface value or a type as input and returns whether it is comparable according to Go.

## Ghost equality `===`, `!==`
The ghost comparison `===` compares values of arbitrary types by identity and does not panic.
``` go verifies
{{#include comparable.go:GhostEq}}
```
If we used the normal equality `==` instead in the preceding example, Gobra would report an error since the sequence contains elements of type `any` that might not be directly comparable.
``` text
ERROR Comparison might panic. 
Both operands of view[i] == view[j] might not have comparable values.
```

## Full example
``` go verifies
{{#include comparable.go:all}}
```

