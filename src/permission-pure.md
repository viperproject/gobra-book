# Pure Functions and Permissions

Pure functions implicitly return all permissions mentioned in the precondition.
Recall that pure functions have no side effects.
Hence they should not leak any permissions.

``` gobra
ghost
requires forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], 1/2)
decreases
pure func isSliceSorted(s []int) bool {
	return forall i, j int :: {&s[i], &s[j]} 0 <= i && i < j && j < len(s) ==> s[i] <= s[j]
}

func client() {
    xs := []int{1, 5, 7, 11, 23, 43, 53, 123, 234, 1024}
    assert isSliceSorted(xs)
    // implicitly transferred back
    assert acc(xs)
}
```

Pure functions could require write permission,
but they cannot actually write as this would be a side effect.
