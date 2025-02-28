# Type assertions, `typeOf`

## `nil` interface values
A `nil` interface value holds neither value nor concrete type [[1]](https://go.dev/tour/methods/13).
In the following example, the variable `c` is not assigned.
``` go
{{#include ./imageFail.go:ConvertFail}}
```
Go panics with a run-time error if a method is called on a `nil` interface value.
Holding no concrete type, there is no way to lookup which concrete method to call.
``` text
panic: runtime error: invalid memory address or nil pointer dereference
```
Gobra statically reports an error instead:
``` text
ERROR Precondition of call c.RGBA() might not hold. 

The receiver might be nil
```

Note that an interface variable holding a concrete type is non-nil, even when the concrete value is `nil`.
In the following example, `*S` implements the interface `I`.
The first two assertion pass since `i` has the dynamic type `*S`.
Hence, it is legal to call the method `M`.
The receiver `(s *S)` might be nil, so the last assertion fails:
``` go
package main

type I interface {
	M()
}

func main() {
	var i I = (*S)(nil)
	// @ assert i != nil
	// @ assert typeOf[i] == type[*S]
	i.M()
}

type S struct{ x int }

func (s *S) M() {
	// @ assert s != nil	// error
}
```
``` text
ERROR Assert might fail.
Assertion s != nil might not hold.
```


## TODO good name
Another interface from the image package of the Go standard library is the `Model`, to convert between different color models (possibly lossy).

``` go
{{#include ./image.go:Model}}
```
The precondition `c != nil` for `Convert` in the `Model` interface excludes the case with the nil interface value as outlined above.


## Type assertions
Given an interface value `v` of underlying type `T`,
we can recover the concrete value `i` of type `T` using a type assertion `i := v.(T)`.
This operation can cause a run-time panic when the underlying type is not `T`.
In the following example, Gobra reports an error since the underlying type of the variable `c` is unknown:
``` go
{{#include ./imageFail.go:TypeAssertionFail}}
```
``` text
ERROR Type assertion might fail. 

Dynamic value might not be a subtype of the target type.
```

By assigning a second variable `i, ok := v.(T)`, the type assertion does no longer panic.
If `ok` is `true` then `i` is the underlying value.
Otherwise if `ok` is `false`, `i` is the `nil` value of type `T`.

As an example, consider the implementation of the `Model` interface for the `alpha16Model`.
`Convert` takes an arbitrary `Color` interface value and converts it to the `Alpha16` color model.
By using a type assertion test, we can return the argument if it is already a `Alpha16` color:
``` go
{{#include ./image.go:alpha16Model}}
```

## Dynamic types with `typeOf`
Gobra provides the `typeOf` function which takes an argument of an interface value and returns its dynamic type.
In the example above, we specified for the `Convert` implementation for `alpha16Model` that the type of the return value is `Alpha16`.
To implement the `Model` interface, the type of the out-parameter must be `Color`.
``` go
// @ ensures typeOf(res) == type[Alpha16]
```
Note that we wrap the type `T` with `type[T]` to refer to it.

With the postcondition the following client code verifies:
``` go
{{#include ./imageFail.go:ConvertClient}}
```
