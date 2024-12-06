# Invariants

An invariant is an assertion that is preserved by the loop across iterations.

The loop invariant is valid if it holds...
1. before the first iteration after performing the initialization statement
2. after every iteration
3. when exiting the loop

In Gobra we can specify it with the `invariant` keyword before a loop.
``` go
//@ invariant ASSERTION
for condition {
	// ..
}
```

Similarly to `requires` and `ensures` you can split an `invariant` on multiple lines.

<!--
``` gobra
func client() {
	{ // to limit the scope
		i := 0 // hoisted initialization

		assert INV

		invariant INV
		for ; i < N; i++ {
			BODY	// assuming no jumps outside
			assert INV
		}
		assert INV
	}
	// assert INV // may fail here, could depend on i that is out of scope
}
``` 
-->
