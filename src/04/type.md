# Type assertions, `typeOf`
Another interface from the image package of the [Go standard library](https://cs.opensource.google/go/go/+/refs/tags/go1.24.0:src/image/color/color.go;drc=9299547e4dec01a7fed8226f8d3080eccf965aa4;l=236) is the `Model`, to convert between different color models.
In this section, we study an implementation of this interface using both type assertions and the `typeOf` function from Gobra.

``` go
{{#include ./type.go:Model}}
{{#include ./type.go:Color}}
```
We cannot convert _any_ color as described in the docstring, but any color with `c != nil` to exclude the case of the [nil interface value](./nil.md).

## Type assertions
Given an interface value `v` of underlying type `T`,
we can recover the concrete value `i` of type `T` using a type assertion `i := v.(T)`.
This operation might cause a run-time panic when the underlying type is not `T`.
In the following example, Gobra reports an error since the underlying type of the variable `c` is unknown:
``` go does_not_verify
{{#include ./type.go:TypeAssertionFail}}
```
``` text
ERROR Type assertion might fail. 

Dynamic value might not be a subtype of the target type.
```

By assigning a second variable `i, ok := v.(T)`, the type assertion no longer panics.
If `ok` is `true` then `i` is the underlying value.
Otherwise, if `ok` is `false`, `i` is the zero value of type `T`.
<!-- [[1]](https://go.dev/tour/methods/15). -->

Consider the implementation of the `Model` interface for the `alpha16Model`, which converts a color to the `Alpha16` color model.
By using a type assertion, we can return the argument if it is already an `Alpha16` color:
``` go verifies
{{#include ./type.go:alpha16Model}}
```

## Dynamic types with `typeOf`
Gobra provides the `typeOf` function, which takes an argument of an interface value and returns its dynamic type.
In the example above, we specified in the `Convert` implementation of `alpha16Model` that the return type is `Alpha16`.
Note that to implement the `Model` interface, the return type must be `Color`, not `Alpha16`.
``` go
// @ ensures typeOf(res) == type[Alpha16]
```
To refer to it, we must wrap the type `T` with `type[T]`.
With this postcondition, the following client code verifies:
``` go verifies
{{#include ./type.go:ConvertClient}}
```

## Full section example

``` go verifies
{{#include ./type.go:all}}
```
