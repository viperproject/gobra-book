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
If we check our [binary search](./loops-binarysearch.md) program for large arrays with overflow checking enabled, Gobra detects a potential overflow.
``` go
package binarysearch

// ##(--overflow)

const N = 1 << 62

// @ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
// @ ensures 0 <= idx && idx <= len(arr)
// @ ensures idx > 0 ==> arr[idx-1] < target
// @ ensures idx < len(arr) ==> target <= arr[idx]
// @ ensures found == (idx < len(arr) && arr[idx] == target)
func BinarySearchOverflow(arr [N]int, target int) (idx int, found bool) {
	low := 0
	high := len(arr)
	mid := 0
	// @ invariant 0 <= low && low <= high && high <= len(arr)
	// @ invariant 0 <= mid && mid < len(arr)
	// @ invariant low > 0 ==> arr[low-1] < target
	// @ invariant high < len(arr) ==> target <= arr[high]
	for low < high {
		mid = (low + high) / 2
		if arr[mid] < target {
			low = mid + 1
		} else {
			high = mid
		}
	}
	if low < len(arr) {
	 	return low, arr[low] == target
	} else {
	 	return low, false
	}
}
```
``` text
ERROR Expression may cause integer overflow.
Expression (low + high) / 2 might cause integer overflow.
```
<!-- TODO if it works without error use: `return low, low < len(arr) && arr[low] == target` otherwise explain why not -->
For example, if `low = (MaxInt64-1)/2` and `high = MaxInt64 - 1` their sum cannot be represented by an `int64` and the result will be negative.
The solution is to replace the offending statement with
`mid = (high-low)/2 + low` where the subtraction does not overflow since `high >= low` and `low >= 0` holds.
After this change, Gobra reports no errors.

If we tweak the `const N` that denotes the array length to `1<<31` which is larger than `MaxInt32` we get an error if we check with the `--int32` flag but otherwise verification succeeds.

This bug was actually in Java's standard library ([Read All About It: Nearly All Binary Searches and Mergesorts are Broken](https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/)).
We think this highlights why heavily used code should be verified.

