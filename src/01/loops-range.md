# Range Loops

Besides traditional `for` loops, Go supports iterating over data structures with for-range loops.
In this section, we consider range clauses for arrays.
We show how to reason about for-range loops that iterate over [slices](../02/slices.md) and [maps](../02/maps.md) in their corresponding sections.
These data structures pose additional challenges, as they may be concurrently accessed, and thus, we need to employ permissions when reasoning about them.
Gobra does not support range clauses for integers, strings, and functions.

Here we refactor the `LinearSearch` example from the section on [loop invariants](./loops-invariant.md) to use a for-range loop.
The contract is left unchanged, but Gobra reports an error:
``` go does_not_verify
const N = 10

// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
func LinearSearch(arr [N]int, target int) (idx int, found bool) {
	// @ invariant 0 <= i && i <= len(arr)
	// @ invariant forall j int :: 0 <= j && j < i ==> arr[j] != target
	for i, a := range arr {
		if a == target {
			return i, true
		}
	}
	return -1, false
}
```
``` text
ERROR Postcondition might not hold. 
Assertion !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target might not hold.
```
We have come across the pattern where the negation of the loop condition, combined with the invariant, often implies the postcondition.
In a standard for loop, we can deduce that `i == len(arr)` holds after the final iteration.
In the range version, however, `i` equals `len(arr) - 1` during the last iteration.
Since the range version has no explicit loop condition, Gobra only _knows_ that `0 <= i && i < len(arr)` holds during the after iteration, which is insufficient to prove the postcondition.

## Helper loop variable from a `with` clause
We can specify an additional loop variable `i0` defined using `with i0` after a `range` clause.
The invariant `0 <= i0 && i0 <= len(arr)` holds, as does `i0 < len(arr) ==> i == i0`.
Additionally, `i0` will be equal to `len(arr)` at the end of the loop.
Thus, if we replace `i` with `i0` in the second invariant, Gobra can verify the postcondition.
The invariant `0 <= i && i < len(arr)` can be removed, as it is implicitly understood by Gobra.
Our final verifying version is:
``` go verifies
package main

const N = 10

// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
func LinearSearchRange(arr [N]int, target int) (idx int, found bool) {
	// @ invariant forall j int :: 0 <= j && j < i0 ==> arr[j] != target
	for i := range arr /*@ with i0 @*/ {  // <--- added with
		if arr[i] == target {
			return i, true
		}
	}
	return -1, false
}

func client() {
	arr := [10]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
	i10, found := LinearSearchRange(arr, 10)
	// @ assert !found
	// @ assert forall i int :: 0 <= i && i < len(arr) ==> arr[i] != 10
	// @ assert arr[4] == 4
	i4, found4 := LinearSearchRange(arr, 4)
	// @ assert found4
	// @ assert arr[i4] == 4
}
```
