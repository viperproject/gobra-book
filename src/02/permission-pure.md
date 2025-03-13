# Pure functions and permissions

Recall that [pure functions](./01/pure.md) have no side effects.
Hence, they must not leak any permissions and implicitly transfer back all permissions mentioned in the precondition.
While pure functions can require write permission, they cannot actually modify values, as this would be a side effect.
It is idiomatic to use [wildcard permissions](wildcard-permission.md) since all the permissions held before a `pure` function call are still held after the call.
<!-- TODO maybe mention that it even an error to have them in the postcondition -->

The `pure` and `ghost` function `allZero` returns whether all elements of an array behind a pointer are zero.
After allocation with `new`, the array is filled with zero values, and this can be asserted.

``` go
package ghostpure

const N = 42

/*@
ghost
requires forall i int :: 0 <= i && i < len(*s) ==> acc(&((*s)[i]), _)
decreases
pure func allZero(s *[N]int) bool {
    return forall i int :: 0 <= i && i < len(*s) ==> (*s)[i] == 0
}
@*/

func client() {
    xs := new([N]int)
    // @ assert acc(xs, 1)
    // @ assert allZero(xs)
    // @ assert acc(xs, 1)
}
```


> Pure functions do not leak any permissions.

<!-- Currently, we have to manually dereference the array pointer before indexing.
TODO simplify after [#805](https://github.com/viperproject/gobra/issues/805)) -->
