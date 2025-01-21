# Pure functions and permissions

> Pure functions implicitly return all permissions mentioned in the precondition.

Recall that [pure functions](./basic-ghost-pure.md)  have no side effects.
Hence they should not leak any permissions.
Pure functions could require write permission,
but they cannot actually write as this would be a side effect.

The `pure` and `ghost` function `allZero` returns whether all elements of an array behind a pointer are zero.
After allocation with `new`, this can be asserted.

``` go
package ghostpure

const N = 42
/*@
ghost
requires forall i int :: 0 <= i && i < len(*s) ==> acc(&((*s)[i]))
decreases
pure func allZero(s *[N]int) bool {
    return forall i int :: 0 <= i && i < len(*s) ==> (*s)[i] == 0
}
@*/

func client() {
    xs := new([N]int)
    // @ assert allZero(xs)
    // implicitly transferred back
    // @ assert acc(xs)
}
```

Currently, we have to manually dereference the array pointer before indexing.
(TODO simplify after [#805](https://github.com/viperproject/gobra/issues/805))
