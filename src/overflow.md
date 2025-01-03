# Overflow Checking
<div class="warning">
Overflow checking is an experimental feature.
It is currently buggy and should be used with care.
</div>

## Usage
On the command line, you can enable overflow checking with the `--overflow` or `-o` flag.

The size of `int` is [implementation-specific](https://go.dev/ref/spec#Numeric_types)  in Go and either 32 or 64 bits.
For overflow checking Gobra assumes 64 bit integers.
This can be overridden with the `--int32` flag.

## Binary Search Example

If we check our binary search program for large arrays with overflow checking enabled, Gobra detects a potential overflow:
``` go
package binarysearch

// ##(--overflow)

const N = 1<<62 - 1
//@ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < N ==> arr[i] <= arr[j]
//@ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != value
func BinarySearchArr(arr [N]int, value int) (found bool) {
	low := 0
	high := len(arr) - 1
	mid := 0
	//@ invariant 0 <= low && low <= high && high < len(arr)
	//@ invariant 0 <= mid && mid < len(arr)
	//@ invariant forall i int :: {arr[i]} 0 <= i && i < low ==> arr[i] < value
	//@ invariant forall i int :: {arr[i]} high < i && i < len(arr) ==>  value < arr[i]
	for low < high {
		mid = (low + high) / 2
		if arr[mid] == value {
			return true
		} else if arr[mid] < value {
			low = mid + 1
		} else {
			high = mid
		}
	}
	return arr[low] == value
}
```
``` text
ERROR Expression may cause integer overflow.
Expression (low + high) / 2 might cause integer overflow.
```
For example, if `low = (MaxInt64-1)/2` and `high = MaxInt64 - 1` their sum cannot be represented by an `int64` and the result will be negative.
The solution is to replace the offending statement with
`mid = (high-low)/2 + low` where the subtraction does not overflow since `high >= low` and `low >= 0` holds.
After this change, Gobra reports no errors.

If we tweak the `const N` that denotes the array length to `1<<31` which is larger than `MaxInt32` we get an error if we check with the `--int32` flag but otherwise verification succeeds.

This bug was actually in Java's standard library ([Read All About It: Nearly All Binary Searches and Mergesorts are Broken](https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/)).
We think this highlights why heavily used code should be verified.

