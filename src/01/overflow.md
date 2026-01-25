# Overflow Checking
<div class="warning">
Overflow checking is still an experimental feature under development.
You may encounter bugs and observe unexpected results.
</div>

## Usage
By default, Gobra performs no overflow checking.
You can enable overflow checking on the command line with the `--overflow` or `-o` flag.
The size of `int` is [implementation-specific](https://go.dev/ref/spec#Numeric_types)  in Go and either 32 or 64 bits.
For overflow checking, Gobra assumes that `int`s have 64 bits by default.
By passing the '-- int32 ' flag, we may change Gobra's behavior to consider `int`s with 32 bits.
In a file, we can enable overflow checking by adding the following line:
``` go
// ##(--overflow)
```

## Overflow in binary search
If we check our [binary search](./loops-binarysearch.md) program for large arrays with overflow checking enabled, Gobra detects a potential overflow.
``` go does_not_verify
package binarysearch

// ##(--overflow)

const MaxInt64 = 1<<63 - 1
const N = MaxInt64

// @ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
// @ ensures 0 <= idx && idx <= len(arr)
// @ ensures idx > 0 ==> arr[idx-1] < target
// @ ensures idx < len(arr) ==> target <= arr[idx]
// @ ensures found == (idx < len(arr) && arr[idx] == target)
func BinarySearchOverflow(arr [N]int, target int) (idx int, found bool) {
	lowElement := 0
	highElement := len(arr)
	mid := 0
	// @ invariant 0 <= lowElement && lowElement <= highElement && highElement <= len(arr)
	// @ invariant 0 <= mid && mid < len(arr)
	// @ invariant lowElement > 0 ==> arr[lowElement-1] < target
	// @ invariant highElement < len(arr) ==> target <= arr[highElement]
	for lowElement < highElement {
		mid = (lowElement + highElement) / 2  // <--- problematic expression
		if arr[mid] < target {
			lowElement = mid + 1
		} else {
			highElement = mid
		}
	}
	if lowElement < len(arr) {
	 	return lowElement, arr[lowElement] == target
	} else {
	 	return lowElement, false
	}
}
```
``` text
ERROR Expression may cause integer overflow.
Expression (lowElement + highElement) / 2 might cause integer overflow.
```
<!-- TODO if it works without error use: `return lowElement, lowElement < len(arr) && arr[lowElement] == target` otherwise explain why not
Relevant issue: https://github.com/viperproject/gobra/issues/816 -->
For example, for `lowElement = N/2` and `highElement = N`, the sum `lowElement + highElement` cannot be represented by an `int`, and the result will be negative.
The solution is to replace the offending statement `mid = (lowElement + highElement) / 2` with:
``` go
mid = (highElement-lowElement) / 2 + lowElement
```
The subtraction does not overflow since `highElement >= lowElement` and `lowElement >= 0` holds.
After this change, Gobra reports no errors.


If we tweak the `const N` that denotes the array length to `1<<31` larger than `MaxInt32`, we get an error when checking with `--int32 --overflow`.
Verification succeeds when only check with `--overflow`.

A similar bug was present in Java's standard library ([Read All About It: Nearly All Binary Searches and Mergesorts are Broken](https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/)).
This highlights why heavily used code such as packages from the standard library should be verified.
