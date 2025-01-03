# Range Loops

In Go, loops can iterate over a `range` clause
Gobra supports `range` for arrays, slices, and maps.
Supported are integers, strings, and functions.

In the section for slices and maps `range` is discussed again.
Here we refactor the `LinearSearch` example from the section on [invariants](./loops-invariant.md) to use a `range` loop for an array.
The contract is left unchanged, but Gobra reports an error:
``` go
// @ ensures idx != -1 ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
func LinearSearch(arr [N]int, target int) (idx int, found bool) {
	//@ invariant 0 <= i && i <= len(arr)
	//@ invariant forall j int :: 0 <= j && j < i ==> arr[j] != target
	for i, a := range arr { // before: for i:=0;i<len(arr);i+=1
		if a == target {    // before: arr[i] == target
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
For loops, the common pattern is that the negation of the loop condition together with the invariant implies the postcondition.
In the standard `for` loop, we can deduce that `i == len(arr)` after the last iteration.
For the `range` version, `i` is equal `len(arr)-1` in the last iteration.
But there is no loop condition, and Gobra only _knows_ that `0 <= i && i < len(arr)` holds after the last iteration which is not enough to prove the postcondition.

## `with`
We can specify an additional loop variable defined using `with i0` after `range`.
The invariant `0 <= i0 && i0 <= len(arr)` holds as well as `i0 < len(arr) ==>  i == i0`.
Additionally, `i0` will be equal to `len(arr)` at the end of the loop.
Hence if we replace `i` with `i0` in the second invariant, Gobra can show the postcondition.
We can remove the invariant `0 <= i && i < len(arr)` as this is implicitly available to Gobra.
Our final verifying version is:
``` go
package main

const N = 10

// @ ensures idx != -1 ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
func LinearSearchRange(arr [N]int, target int) (idx int, found bool) {
	//@ invariant forall j int :: 0 <= j && j < i0 ==> arr[j] != target
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
	//@ assert !found
	//@ assert forall i int :: 0 <= i && i < len(arr) ==> arr[i] != 10
	//@ assert arr[4] == 4
	i4, found4 := LinearSearchRange(arr, 4)
	//@ assert found4
	//@ assert arr[i4] == 4
}
```
