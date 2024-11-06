# Range Loops

We are given code that verifies containing the following loop iterating over an integer array:
``` go
//@ invariant 0 <= i && i <= len(arr)
//@ invariant forall k int :: 0 <= k && k < i ==> res >= arr[k]
for i := 0; i < len(arr); i += 1 {
    if arr[i] > res {
        res = arr[i]
    }
}
```
But we want to refactor it using the idiomatic `range` clause:
``` go
//@ invariant 0 <= i && i <= len(arr)
//@ invariant forall k int :: 0 <= k && k < i ==> res >= arr[k]
for i, a := range(arr) {
    if a > res {
        res = a
    }
}
```

``` text
Postcondition might not hold. 
Assertion forall i int :: 0 <= i && i < len(arr) ==> res >= arr[i] might not hold.
```
For loops, the general pattern is that the negation of the loop condition together with the invariant implies the postcondition.

We have to specify an additional iteration variable, here `i0`, after `range`, defined using `with`.
Let us replace `i` with `i0` in the second invariant:

``` go
//@ invariant 0 <= i && i <= len(arr)
//@ invariant forall k int :: 0 <= k && k < i0 ==> res >= arr[k]
for i, a := range(arr) /*@ with i0 @*/ {
    if a > res {
        res = a
    }
}
```
<!-- At the beginning of the loop body `i0 == i` holds. -->

This allows Gobra to infer the postcondition.
The first invariant is no longer necessary and we can ignore `i`.

Our final, verifying version:
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
