# Range Loops
Go supports loops iterating over a range clause.
In this section we use arrays, later we will also iterate over slices and maps.
Gobra does not support ranges over integers, strings, slices and functions.


We are given code that verifies containing the following loop iterating over an integer array:
``` go
// @ requires len(arr) > 0
// @ ensures forall i int :: 0 <= i && i < len(arr) ==> res >= arr[i]
func almostMax(arr [N]int) (res int) {
    //@ invariant 0 <= i && i <= len(arr)
    //@ invariant forall k int :: 0 <= k && k < i ==> res >= arr[k]
    for i := 0; i < len(arr); i += 1 {
        if arr[i] > res {
            res = arr[i]
        }
    }
    return
}
```
But we want to refactor it using a `range` clause we face an error:
``` go
~// @ requires len(arr) > 0
~// @ ensures forall i int :: 0 <= i && i < len(arr) ==> res >= arr[i]
~func almostMax(arr [N]int) (res int) {
    //@ invariant 0 <= i && i <= len(arr)
    //@ invariant forall k int :: 0 <= k && k < i ==> res >= arr[k]
    for i, a := range(arr) {
        if a > res {
            res = a
        }
    }
    ~return
~}
```
``` text
Postcondition might not hold. 
Assertion forall i int :: 0 <= i && i < len(arr) ==> res >= arr[i] might not hold.
```
For loops, the general pattern is that the negation of the loop condition together with the invariant implies the postcondition.
In the standard for loop, `i` is equal to `len(arr)` in the last iteration while
for it is `len(arr)-1` in the range version.

We can specify an additional iteration variable (here `i0`) defined using `with i0` after `range`.
At the beginning of an iteration `i0 == i` holds and Unlike `i` one cannot modify `i0`.
Additionally `i0` will equal `len(arr)` at the end of the loop.
Hence if we replace `i` with `i0` in the second invariant, Gobra can infer the postcondition.
We no longer need the invariant constraining `i` and our final verifying version is:
``` go
~package main
~const N = 42
// @ requires len(arr) > 0
// @ ensures forall i int :: 0 <= i && i < len(arr) ==> res >= arr[i]
func almostMax(arr [N]int) (res int) {
	res = arr[0]
	//@ invariant forall k int :: 0 <= k && k < i0 ==> res >= arr[k]
	for _, a := range arr /*@ with i0 @*/ {
		if a > res {
			res = a
		}
	}
    return
}
```
