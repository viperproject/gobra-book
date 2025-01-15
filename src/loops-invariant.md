# Loop Invariants

An _invariant_ is an assertion that is preserved by the loop across iterations.

> Gobra checks that the invariant holds
> 1. before the first iteration after performing the initialization statement
> 2. after every iteration

<!-- If the loop is exited early with a `break` or `return` statement, the invariant may not hold. -->

We can specify it with the keyword `invariant` before a loop.
``` go
// @ invariant ASSERTION
for condition { // ... }
```

Similarly to `requires` and `ensures` you can split an invariant on multiple lines.

Finding loop invariants, in general, can be pretty hard.
In the general case, there is no procedure to figure out which invariants are needed in order to verify a program against a specification.
Nonetheless, it does get much easier the more you do it, and we hope to show it on a few examples step-by-step.

As a first example, the function `LinearSearch` searches an array for a value `target`.
If `target` is found, `idx` shall be its index.
Otherwise, no element of the array must be equal to `target`.
This function bears similarity to `Contains` from the section on [quantifiers](quantifier.md),
with the difference that we additionally return the index, which allows us to avoid an existential quantifier.
Here we will be able to prove the contract for the case `found ==> ....` as well by providing appropriate loop invariants.

``` go
package linearsearch

// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
func LinearSearch(arr [10]int, target int) (idx int, found bool) {
	// @ invariant 0 <= i && i <= len(arr)
	// @ invariant forall j int :: 0 <= j && j < i ==> arr[j] != target
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
	// @ assert !found
	// @ assert forall i int :: 0 <= i && i < len(arr) ==> arr[i] != 10
	// @ assert arr[4] == 4
	i4, found4 := LinearSearch(arr, 4)
	// @ assert found4
	// @ assert arr[i4] == 4
}
```
Gobra cannot track all possible values for the loop variable `i` over all iterations and we must help by specifying bounds for `i` with:
``` gobra
invariant 0 <= i && i <= len(arr)
```
Without this invariant, Gobra reports the error:
``` text
ERROR Loop invariant is not well-formed. 
Index j into arr[j] might exceed sequence length.
```
Let us check manually whether this invariant holds:
1. We initialize `i := 0`, so the invariant holds before the first loop iteration.
2. The loop guard is `i < len(arr)`. After the statement `i += 1`, the condition `i <= len(arr)` holds. From the invariant, we know that `0 <= i` held before this iteration. Therefore, after incrementing, `1 <= i` holds. Combining these observations, we conclude that `0 <= i && i <= len(arr)` holds after an arbitrary iteration, preserving the invariant.

<br/>

``` gobra
invariant forall j int :: 0 <= j && j < i ==> arr[j] != target
```
Without this second invariant, Gobra cannot prove a postcondition:
``` text
ERROR Postcondition might not hold. 
Assertion !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target might not hold.
!found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
```
This invariant captures the "work" the loop has done so far: all elements with index smaller than `i` have been checked and are not equal to `target`.

When the loop condition `i < len(arr)` fails, `i >= len(arr)` holds.
The first invariant states that `i <= len(arr)`.
Therefore `i == len(arr)` and `forall i int :: 0 <= i && i < len(arr) ==> arr[i] != target` holds.


## Failing to establish an invariant
When we change the first invariant to use `1 <= i` instead of `0 <= i`, this invariant does not hold before the first iteration:
``` go
func NotEstablished(arr [N]int, target int) (idx int, found bool) {
	// @ invariant 1 <= i && i <= len(arr)
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

## Failing to preserve an invariant
When we change the first invariant to use `i < len(arr)` instead of `i <= len(arr)`, this invariant does not hold after every iteration.
After the last iteration `i==len(arr)` holds and this invariant is not preserved.
``` go
func NotPreserved(arr [N]int, target int) (idx int, found bool) {
	// @ invariant 0 <= i && i < len(arr)
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
	
