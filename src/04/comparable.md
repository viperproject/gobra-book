# Comparable interfaces, `isComparable`

Comparing two interfaces may cause a runtime error if both dynamic values are incomparable.
For example, slices are not comparable in Go:
``` go
{{#include comparable.go:main}}
```
``` text
panic: runtime error: comparing uncomparable type []int

goroutine 1 [running]:
main.main()
	/home/gobra/comparable.go:52 +0x77
exit status 2
```

Gobra provides the function `isComparable`, which takes as input an interface value or a type and returns whether it is comparable according to Go.
When the value of an implementation is stored in an interface value, Gobra records whether the resulting interface value is comparable.
In the following example, we assign the numeric constant `5` to `x`, which makes it comparable.

``` go
{{#include comparable.go:isComparable}}
```

As an example, we change the linked [`List`](../03/full-example.md) type to store values of type `any` (which is a shorthand for the empty interface `interface{}`).
``` go
{{#include comparable.go:type}}
```
Note that we can store arbitrary values in the list, as the empty interface is trivially implemented by every type.

The recursive function `Contains` that searches the list for a `value` might panic because of the comparison `l.Value == value` between possibly incomparable values, which Gobra detects:
``` go
// @ requires acc(l.Mem(), 1/2)
// @ pure
// @ decreases l.Mem()
{{#include comparable.go:Contains1}}
```
``` text
ERROR Comparison might panic.
 Both operands of l.Value == value might not have comparable values.
```

To require that the `List` contains only comparable elements, we define the function `Comparable`.
With `isComparable`, we state recursively that each element must be comparable.
``` go
{{#include comparable.go:Comparable}}
{{#include comparable.go:Contains}}
```

The following client code verifies.
``` go
{{#include comparable.go:client}}
```

> Comparing two interfaces may cause a runtime error if both dynamic values are incomparable.
> 
> The function `isComparable` takes as input an interface value or a type and returns whether it is comparable according to Go.


## Full example
``` go
{{#include comparable.go:all}}
```

