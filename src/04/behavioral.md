# Behavioral subtypes

Interfaces in Go are defined as a set of method signatures.
In Gobra, we can add signatures and contracts to the interface definitions.
It must be proven that the implementation is a *behavioral subtype* of the interface, i.e., it provides not only at least the same methods, but also at least the same behavior:
- The precondition of each interface method must imply the precondition of each corresponding implementation method
- The postcondition of each implementation method must imply the postcondition of each corresponding interface method.

In this section, we look at interfaces from the [`image` package from the Go standard library](https://pkg.go.dev/image).
As a first example, we consider the `Color` interface with a single method `RGBA` that returns color components for red, green, blue, and alpha.
``` go
{{#include ./behavioral.go:Color}}
```
We add a contract to the signature that formalizes the docstring, which states that each value falls within the range `[0, 0xffff]`
and "an alpha-premultiplied color component c has been scaled by alpha (a), so has valid values `0 <= c <= a`."
Furthermore, we add a ghost and pure method `Valid` to the interface.
With `Valid`, implementations provide an assertion that must hold for the data structure such that a valid color can be returned.
<!-- We must add `0 <= r` since Gobra currently does not infer this automatically for the unsigned integer type `uint32`. -->

The type `Alpha16`, which represents a 16-bit alpha color:
``` go
{{#include ./behavioral.go:Alpha16}}
```
In Go, interface implementation is implicit, i.e., the `Color` interface is implemented by defining an `RGBA` method.
For Gobra, any ghost methods such as `Valid` must be implemented as well.

``` go
{{#include ./behavioral.go:Alpha16Valid}}
```
Gobra checks that `Alpha16` is a behavioral subtype of `Color` only when needed, that is, when an value of interface type has `Alpha16` as its underlying type.
For example, this occurs when we assign a value to a variable of interface type or pass an argument to a function with an in-parameter of interface type.

The following client verifies since the postcondition of `Alpha16`'s `RGBA` is equivalent to the postcondition of the interface method.
``` go
{{#include ./behavioral.go:client1}}
```

The implementation's postcondition may be stronger.
For example, the `Constant` color guarantees that it always returns the same color components.
From this, the postcondition of the interface immediately follows.
``` go
{{#include ./behavioral.go:Constant}}
```

Similarly, the implementation's precondition may be weaker.

## Implementation precondition too strong
Gobra reports an error if the precondition of an implementation method might not follow from the precondition of the corresponding interface method.

In the following example, `acc(c.p)` is required to call `RGBA` with receivers of type `Fail1`.
The function `client` has a parameter of interface type, whose concrete type is unknown. 
When `c.RGBA()` is called, the precondition of the interface method must hold.
However, this does not imply the precondition of `Fail1`'s `RGBA`.
Hence, it would be unsound to allow `Fail1` to be used as a value of type `Color`.
``` go
{{#include ./behavioral.go:fail1}}
```
``` text
ERROR Generated implementation proof (Fail1 implements interface{ RGBA }) failed. Precondition of call to implementation method might not hold. 
Permission to c.p might not suffice.

ERROR Precondition of call c.RGBA() might not hold. 
Assertion Valid() might not hold.
```

## Implementation postcondition too weak
An error is reported if the postcondition of an implementation method might not imply the postcondition of the corresponding interface method.
<!-- unsound (well here it would actually hold, just not specified...) -->
``` go
{{#include ./behavioral.go:fail2}}
```
``` text
ERROR Generated implementation proof (Fail2 implements interface{ RGBA }) failed. Postcondition of interface method might not hold. 

Assertion a <= 0xffff might not hold.
```

In the above example, the postcondition `a <= 0xffff` is missing from the contract of the implementation.
It does not follow from the given postcondition:
``` go
// @ ensures 0 <= r && r <= a && 0 <= g && g <= a && 0 <= b && b <= a
```

So far, we have relied on generated implementation proofs from Gobra.
In a following section, we show how to provide our own [implementation proofs](./implements.md).

> The precondition of the interface method must imply the precondition of the implementation method.
>
> The postcondition of the implementation method must imply the postcondition of the interface method.


## Full section example
``` go
{{#include ./behavioral.go:all}}
```
