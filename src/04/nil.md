# `nil` interface values

A `nil` interface value holds neither a value nor a concrete type [[1]](https://go.dev/tour/methods/13).
For example, the variable `c` of type `Color` is not assigned a concrete value.
``` go
{{#include ./nil.go:fail1}}
```
Go panics with a run-time error if a method is called on a `nil` interface value.
Since it holds no concrete type, there is no way to look up which concrete `RGBA` method to call.
``` text
panic: runtime error: invalid memory address or nil pointer dereference
```
Gobra statically reports an error instead:
``` text
ERROR Precondition of call c.RGBA() might not hold. 

The receiver might be nil
```

Note that an interface variable holding a concrete type is non-nil, even when the concrete value is `nil`.
In the following example, `*SomeColor` implements the interface `Color`.
The first two assertions pass since `c` has the dynamic type `*SomeColor`.
Hence, calling the method `RGBA` is legal.
Since the receiver `(s *SomeColor)` might be `nil`, the last assertion fails:
``` go
{{#include ./nil.go:fail2}}
```
``` text
ERROR Assert might fail.

Assertion s != nil might not hold.
```

## Full section example

``` go
{{#include ./nil.go:all}}
```
