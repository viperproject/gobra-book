# Overflow Checking
<div class="warning">
Overflow checking is an experimental feature.
It is currently buggy and should be used with care.
</div>

## Usage
On the command line you can enable overflow checking with the `--overflow` or `-o` flag.

The size of `int` is [implementation-specific](https://go.dev/ref/spec#Numeric_types)  in Go and either 32 or 64 bits.
For overflow checking Gobra assumes 64 bit integers.
This can be overridden with the `--int32` flag.

## Binary Search Example

If we check our binary search program with overflow checking enabled, Gobra reports that

``` text
Expression (low + high) / 2 might cause integer overflow.
```
For example if `low = 2` and `high = MaxInt64 - 1`
their sum cannot be represented by an `int64` and the result will be negative.

<!-- full code ../code/binary-search-termination.gobra -->
The solution is to replace the offending statement with
`mid = (high-low)/2 + low`.

After this change, Gobra reports no errors.

If we tweak the `const N` that denotes the array length to `2147483648` which is larger than `MaxInt32` we get an error if we check with the `--int32` flag but otherwise verification succeeds.

This bug was actually in Java's standard library ([Read All About It: Nearly All Binary Searches and Mergesorts are Broken](https://research.google/blog/extra-extra-read-all-about-it-nearly-all-binary-searches-and-mergesorts-are-broken/)).
We think this highlights why heavily used code should be verified.


## Absolute Value
Can you spot the overflow in the following example?
``` gobra
const MinInt64 = -9223372036854775808 // = -1 << 63 
ensures res >= 0
func abs(x int64) (res int64) {
	if x < 0 {
		return -x
	} else {
		return x
	}
}
```

``` text
Expression -x might cause integer overflow.
```
This is because by two's complement arithmetic there is one more negative integer and `abs(MinInt64)` overflows.

<!-- result is actually MinInt64 -->
The program verifies when we add the precondition
``` gobra
requires x > MinInt64 + 1
```

<!--
requires x != MinInt64  DOES NOT WORK
also
requires x > MinInt64
somehow we need the + 1
but abs(MinInt64 + 1) works as expected
Off-by-one error somewhere?
-->
