# Pure functions and permissions

Recall that [pure functions](../01/pure.md) have no side effects.
Hence, they must not leak any permissions and implicitly transfer back all permissions mentioned in the precondition.
While pure functions can require write permission, they cannot modify values, as this would be a side effect.
Using [wildcard permissions](wildcard-permission.md) is idiomatic since all permissions held before a `pure` function call are still held after the call.

The `pure` and `ghost` function `allZero` returns whether all elements of an array behind a pointer are zero.
After being allocated with `new,` the array is filled with zero values, and this can be asserted.

``` go verifies
{{#include allZero.go}}
```


> Pure functions do not leak any permissions.

