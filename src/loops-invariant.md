# Invariants

An _invariant_ is an assertion that is preserved by the loop across iterations.

> Gobra checks that the invariant holds
> 1. before the first iteration after performing the initialization statement
> 2. after every iteration

If the loop is exited early with a `break` or `return` statement, the invariant may not hold.

In Gobra we can specify it with the `invariant` keyword before a loop.
``` go
//@ invariant ASSERTION
for condition { // ... }
```

Similarly to `requires` and `ensures` you can split an invariants on multiple lines.

We write a function `LinearSearch` that searches an array for a value `target`.
If `target` is found, `idx` is its index. Otherwise, no element of the array must be equal to `target`.

``` go
package main
const N = 10

// @ ensures idx != -1 ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
func LinearSearch(arr [N]int, target int) (idx int, found bool) {
	//@ invariant 0 <= i && i <= len(arr)
	//@ invariant forall j int :: 0 <= j && j < i ==> arr[j] != target
	for i := 0; i < len(arr); i += 1 {
		if arr[i] == target {
			return i, true
		}
	}
	return -1, false
}

func client() {
	arr := [10]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
	i10, found := LinearSearch(arr, 10)
	//@ assert !found
	//@ assert forall i int :: 0 <= i && i < len(arr) ==> arr[i] != 10
	//@ assert arr[4] == 4
	i4, found4 := LinearSearch(arr, 4)
	//@ assert found4
	//@ assert arr[i4] == 4
}
```

The loop variable `i` is initialized with `0` and incremented after every iteration.
We can help the verifier by specifying bounds for `i` with `invariant 0 <= i && i <= len(arr)`.
Without this invariant, Gobra reports the error:
``` text
ERROR Loop invariant is not well-formed. 
Index j into arr[j] might exceed sequence length.
```
Let us check the invariant rules:
1. We initialize `i := 0`, hence the invariant holds before the first loop iteration.
2. The loop guard is `i < len(arr)` and `i`. Then after the post statement `i += 1`, `i <= len(arr)` holds. From the invariant we know that before this iteration `0 <= i` held, so afterwards `1 <= i` holds. This implies that `0 <= i && i <= len(arr)` holds after an iteration.


Without the second invariant `forall j int :: 0 <= j && j < i ==> arr[j] != target`,
Gobra cannot prove that the postcondition `!found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target` holds.
It captures the "work" the loop has done so far: all elements with index smaller than `i` have been checked and are not equal to `target`.

When the loop condition `i < len(arr)` fails, `i >= len(arr)` holds.
The first invariant states that `i <= len(arr)`.
Therefore `i == len(arr)` and `forall i int :: 0 <= i && i < len(arr) ==> arr[i] != target` holds.

## Failing to establish invariant
When we change the first invariant to use `1 <= i` instead of `0 <= i`, this invariant does not hold before the first iteration:
``` go
func NotEstablished(arr [N]int, target int) (idx int, found bool) {
	//@ invariant 1 <= i && i <= len(arr)
	for i := 0; i < len(arr); i += 1 {
		if arr[i] == target {
			return i, true
		}
	}
	return -1, false
}
```
``` text
ERROR Loop invariant might not be established. 
Assertion 1 <= i might not hold.
```

## Failing to preserve invariant
When we change the first invariant to use `i < len(arr)` instead of `i <= len(arr)`, this invariant does not hold after every iteration.
After the last iteration `i==len(arr)` holds and this invariant is not preserved.
``` go
func NotPreserved(arr [N]int, target int) (idx int, found bool) {
	//@ invariant 0 <= i && i < len(arr)
	for i := 0; i < len(arr); i += 1 {
		if arr[i] == target {
			return i, true
		}
	}
	return -1, false
}
```
``` text
ERROR Loop invariant might not be preserved. 
Assertion i < len(arr) might not hold.
```

<!-- ``` text -->
<!-- ERROR Postcondition might not hold.  -->
<!-- Assertion !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target might not hold. -->
<!-- ``` -->

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
