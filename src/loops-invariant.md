# Invariants

An invariant is an assertion that is preserved by the loop across iterations.

For the loop to verified, the invariant must hold...
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
decreases
pure func isSorted(arr [N]int) (ghost res bool) {
	return forall j, k int :: 0 <= j && j < k && k < N ==> arr[j] <= arr[k]
}
const N = 100
func client() {
	var arr [N]int
	{
		i := 0

		assert forall j int :: 0 <= j && j < i ==> arr[j] == j

		invariant 0 <= i && i <= len(arr)
		invariant forall j int :: 0 <= j && j < i ==> arr[j] == j
		for ; i < N; i++ {
			// arr[i] = 2*i + 1 // Expression may cause integer overflow.
			arr[i] = i
			assert forall j int :: 0 <= j && j < i ==> arr[j] == j
		}
		assert forall j int :: 0 <= j && j < i ==> arr[j] == j
		assert i == len(arr)
	}
	assert forall j int :: 0 <= j && j < len(arr) ==> arr[j] == j
	assert isSorted(arr)
}
``` 
-->
