# Loops

## Invariants and Isqrt
[//]: # ( example from https://en.wikipedia.org/wiki/Integer_square_root)

[//]: # ( introduce isqrt )


[//]: # ( how to even make specs for it )

### Linear Search


```gobra
requires(x >= 0)
ensures(r * r <= x)
ensures(x < (r + 1) * (r + 1))
func isqrt(x int) (r int) {
	r := 0
	invariant r * r <= x
	for ; (r + 1) * (r + 1) <= x; r += 1 {} // linear search
}
```

[//]: # ( exercise: we change the search to from above (what are now the correct invariants))

```gobra
requires(x >= 0)
ensures(r * r <= x)
ensures(x < (r + 1) * (r + 1))
func isqrt(x int) (r int) {
	// WORKS:
	// from below (from above with t := x and similar)
	// invariant()
	// r := 0
	// invariant r * r <= x
	// for ; (r + 1) * (r + 1) <= x; r += 1 {} // linear search

	r := 0
	a := 1
	d := 3

	// WORKS:
	// Optimization: replace multiplication by addition
	// invariant a == (r + 1) * (r + 1)
	// invariant d == 2 * r + 3
	// invariant r * r <= x
	// for a <= x  {
	// 	a = a + d
	// 	d = d + 2
	// 	r = r + 1
	// }
	// return

	// Binary Search
	low := 0
	var mid int
	high := x + 1

	// which error do we get first: invariant or postcondition?
	// let's test: (yes, reported first)
	// invariant false
	// for {}

	invariant low*low <= x
	invariant x < high * high
	invariant low <= high // THE KEY
	for low < high {
		mid = (low + high) / 2
		if mid * mid <= x {
			low = mid
		} else {
			high = mid
		}
	}
	return low

}
```
### Strength Reduction
Optimization: replace multiplication by addition

```gobra
requires(x >= 0)
ensures(r * r <= x)
ensures(x < (r + 1) * (r + 1))
func isqrt(x int) (r int) {
	r := 0
	a := 1
	d := 3

	invariant a == (r + 1) * (r + 1)
	invariant d == 2 * r + 3
	invariant r * r <= x
	for a <= x  {
		a = a + d
		d = d + 2
		r = r + 1
	}
	return

}
```
### Binary Search
```gobra
requires(x >= 0)
ensures(r * r <= x)
ensures(x < (r + 1) * (r + 1))
func isqrt(x int) (r int) {
	low := 0
	var mid int
	high := x + 1


	invariant low*low <= x
	invariant x < high * high
	invariant low <= high // THE KEY
	for low < high {
		mid = (low + high) / 2
		if mid * mid <= x {
			low = mid
		} else {
			high = mid
		}
	}
	return low

}
```

## Termination

`decreases`
Mention Halting Problem, collatz example
