# Slices

Slices provide an abstraction over a contiguous sequence of data.
A slice has a length, a capacity, and uses an underlying array as storage.

In the following example, a constant `n` is added to all elements of a slice.
Note that the functions `len` and `cap` may be used in contracts.
Access to slice elements is specified using [quantified permissions](./quantified-permission.md).
We obtain permission to the slice elements on allocation, here with `make`.
Note that the loop must preserve the permissions with an invariant.
``` go
// @ preserves forall k int :: {&s[k]} 0 <= k && k < len(s) ==> acc(&s[k])
// @ ensures forall k int :: {&s[k]} 0 <= k && k < len(s) ==> s[k] == old(s[k]) + n
func addToSlice(s []int, n int) {
	// @ invariant 0 <= i && i <= len(s)
	// @ invariant forall k int :: {&s[k]} 0 <= k && k < len(s) ==> acc(&s[k])
	// @ invariant forall k int :: {&s[k]} i <= k && k < len(s) ==> s[k] == old(s[k])
	// @ invariant forall k int :: {&s[k]} 0 <= k && k < i ==> s[k] == old(s[k]) + n
	for i := 0; i < len(s); i += 1 {
		s[i] = s[i] + n
	}
}

func client() {
	s := make([]int, 4, 8)
	// @ assert len(s) == 4 && cap(s) == 8
	addToSlice(s, 1)
	// @ assert forall i int :: {&s[i]} 0 <= i && i < 4 ==> s[i] == 1
}
```

After initialization with a literal, we also gain permission.
``` go
s1 := []int{0, 1, 1, 2, 3, 5}
// @ assert forall i int :: {&s1[i]} 0 <= i && i < len(s1) ==> acc(&s1[i])
```

## Syntactic sugar for slice access
For a slice `s1`, `acc(s1)` is syntactic sugar for:
``` go
forall i int :: {&s1[i]} 0 <= i && i < len(s1) ==> acc(&s1[i])
```
The `assert` statements are equivalent:
``` go
s1 := []int{0, 1, 1, 2, 3, 5}
// @ assert forall i int :: {&s1[i]} 0 <= i && i < len(s1) ==> acc(&s1[i])
// @ assert acc(s1)
```

## Slicing
A slice can be created from another slice or array by slicing it, in general with an expression of the form `a[i:j:k]`.
To check slicing does not panic, Gobra checks as part of the contract of the slicing operation that `0 <= i && i <= j && j <= k && k <= cap(a)` holds.

We may create two overlapping slices `l` and `r` but run into a permission error:
``` go
func overlappingFail() {
    s := make([]int, 3)
    l := s[:2]
    r := s[1:]
    addToSlice(l, 1)
    addToSlice(r, 1) // error
}
```
``` go
ERROR Assert might fail. 
Permission to r might not suffice.
```
While we cannot assert `acc(l) && acc(r)`,
to call `addToSlice` we only need permission for either of the slices, and it should be possible to assert `acc(l)` and `acc(r)` separately.
In order to get permission for the slice `r`, we must explicitly assert how the addresses to the elements of `r` relate to those of `s`:
``` gobra
assert forall i int :: {&r[i]} 0 <= i && i < len(r) ==> &r[i] == &s[i+1]
```
With this proof annotation, the function verifies:
``` go
func overlappingSucceed() {
	s := make([]int, 3)
	l := s[:2]
	r := s[1:]
	// @ assert forall i int :: {&r[i]} 0 <= i && i < len(r) ==> &r[i] == &s[i+1]
	addToSlice(l, 1)
	// @ assert s[0] == 1 && s[1] == 1
	addToSlice(r, 1)
	// @ assert r[0] == 2 && r[1] == 1
	// @ assert s[0] == 1 && s[1] == 2 && s[2] == 1
}
```

## `copy` and `append`
Go includes the `copy` and `append` built-in functions.

We give the contracts for `copy` and `append` for a generic type `T` (Gobra does not yet support generics).
In Gobra, we must pass an additional ghost parameter that specifies the permission amount required to read the elements of `src`.
This allows the functions to generally be used independent of the exact permission amount
``` gobra
requires p > 0
requires forall i int :: {&src[i]} 0 <= i && i < len(src) ==> acc(&src[i])
requires forall i int :: {&xs[i]} 0 <= i && i < len(xs) ==> acc(&xs[i], p)
ensures len(res) == len(src) + len(xs)
ensures forall i int :: {&res[i]} 0 <= i && i < len(res) ==> acc(&res[i])
ensures forall i int :: {&xs[i]} 0 <= i && i < len(xs) ==> acc(&xs[i], p)
ensures forall i int :: {&res[i]} 0 <= i && i < len(src) ==> res[i] === old(src[i])
ensures forall i int :: {&res[i]} len(src) <= i && i < len(res) ==> res[i] === xs[i - len(src)]
func append[T any](ghost p perm, src []T, xs ...T) (res []T)
```

Note that since `append` is variadic, the permission amount must be the first argument.
The permission to `src` is lost, as the underlying array could be reallocated if the capacity is not sufficient to append the new elements.
`s = append(s, 42)` is a common pattern in Go, and this way permissions to `s` are preserved.

`copy` copies the elements from `src` to `dst`.
It stops when the end of the shorter slice is reached and returns the number of elements copied.
 ``` gobra
requires 0 < p
requires forall i int :: {&dst[i]} (0 <= i && i < len(dst)) ==> acc(&dst[i], write)
requires forall i int :: {&src[i]} (0 <= i && i < len(src)) ==> acc(&src[i], p)
ensures len(dst) <= len(src) ==> res == len(dst)
ensures len(src) < len(dst) ==> res == len(src)
ensures forall i int :: {&dst[i]} 0 <= i && i < len(dst) ==> acc(&dst[i], write)
ensures forall i int :: {&src[i]} 0 <= i && i < len(src) ==> acc(&src[i], p)
ensures forall i int :: {&dst[i]} (0 <= i && i < len(src) && i < len(dst)) ==> dst[i] === old(src[i])
ensures forall i int :: {&dst[i]} (len(src) <= i && i < len(dst)) ==> dst[i] === old(dst[i])
func copy[T any](dst, src []T, ghost p perm) (res int)
 ```
<!-- TODO why, in the permission type section it works with 1/2 only?! -->
<!-- as is allowed in the access predicate. -->
The permissions amount must be explicitly passed as `perm(1/2)` instead of only `1/2`.
This simple example shows the usage of `copy` and `append`:
``` go
s1 := []int{1, 2}
s2 := []int{3, 4, 5}
                                                                         
s0 := make([]int, len(s1))
copy(s0, s1 /*@, perm(1/2) @*/)
// @ assert forall i int :: {&s0[i]} {&s1[i]} 0 <= i && i < len(s0) ==> s0[i] == s1[i]
                                                                         
s3 := append(/*@ perm(1/2), @*/ s1, s2...)
s4 := append(/*@ perm(1/2), @*/ s0, 3, 4, 5)
// @ assert forall i int :: {&s3[i]} {&s4[i]} 0 <= i && i < len(s3) ==> s3[i] == s4[i]
```

Using the nil slice, we could refactor the `make` and `copy` operations into the single line `s0 := append([]int(nil), s1...)`.
As opposed to the nil pointer, we may hold permission for the nil slice:
``` go
var s2 []int
// @ assert acc(s2)
// @ assert s2 == nil && len(s2) == 0 && cap(s2) == 0
```

In Go it is possible to append a slice to itself.
The contract of `append` forbids this.
``` go
s1 := []int{1, 2}
s2 := append(/*@ perm(1/64), @*/ s1, s1...)
```
``` text
ERROR Precondition of call append(  perm(1/64),  s1, s1...) might not hold. 
Permission to append(  perm(1/64),  s1, s2...) might not suffice
```

Similarly, in Go the behavior of `copy` is independent of whether the underlying memory of the slices overlaps.
Again, Gobra's contract of `copy` forbids this:
``` go
s := []int{1, 2, 3, 4}
s1 := s[1:]
// @ assert acc(s1)
copy(s, s1 /*@, perm(1/2) @*/)
// fmt.Println(s) // [2 3 4 4]
```
``` text
ERROR Precondition of call copy(s, s1 , perm(1/2) ) might not hold. 
Permission to copy(s0, s1 , perm(1/2) ) might not suffice.
```

## Range clause for slices
Gobra supports the `range` clause for slices.
We refactor the loop in `addToSlice`:
``` go
// @ requires len(s) > 0
// @ preserves acc(s)
// @ ensures forall k int :: {&s[k]} 0 <= k && k < len(s) ==> s[k] == old(s[k]) + n
func addToSlice(s []int, n int) {
	// @ invariant acc(s)
	// @ invariant forall k int :: {&s[k]} i0 <= k && k < len(s) ==> s[k] == old(s[k])
	// @ invariant forall k int :: {&s[k]} 0 <= k && k < i0 ==> s[k] == old(s[k]) + n
	for i, e := range s /*@ with i0 @*/ {
		s[i] = e + n
	}
}
```

Note that we added the precondition `len(s) > 0`.
Otherwise there is the error: 
``` text
ERROR Loop invariant might not be established. 
Permission to s[k] might not suffice.
```
For the case where `len(s) == 0`, `i, e` and `i0` are never assigned values.
As a result, the second invariant cannot be established because `i0` is arbitrary.
For example, `s[k]` could be instantiated as `s[-1]`, even though no permission is held for `&s[-1]`.

Alternatively, we could handle the empty case specifically:
``` go
// @ preserves acc(s)
// @ ensures forall k int :: {&s[k]} 0 <= k && k < len(s) ==> s[k] == old(s[k]) + n
func addToSlice(s []int, n int) {
	if len(s) == 0 {
		return
	}
	// ...
	~// @ invariant acc(s)
	~// @ invariant forall k int :: {&s[k]} i0 <= k && k < len(s) ==> s[k] == old(s[k])
	~// @ invariant forall k int :: {&s[k]} 0 <= k && k < i0 ==> s[k] == old(s[k]) + n
	~for i, e := range s /*@ with i0 @*/ {
		~s[i] = e + n
	~}
}
```

## Binary search over slices
We conclude this section by revisiting the [binary search example](./loops-binarysearch.md).
Now we can perform a `BinarySearch` sorted slices of arbitrary length for a target value.
This version is more efficient because no arrays need to be copied.

We define a `pure` and `ghost` function `isSliceSorted`, to use in the contract of `BinarySearch`.
Unlike `BinarySearchArr`, we add a condition to handle the empty slice and specify access to the slice elements.

``` go
package binarysearchslice

/*@
ghost
requires forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], 1/2)
decreases
pure func isSliceSorted(s []int) bool {
	return forall i, j int :: {&s[i], &s[j]} 0 <= i && i < j && j < len(s) ==> s[i] <= s[j]
}
@*/

// @ requires forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], 1/2)
// @ requires isSliceSorted(s)
// @ ensures forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], 1/2)
// @ ensures 0 <= idx && idx <= len(s)
// @ ensures idx > 0 ==> s[idx-1] < target
// @ ensures idx < len(s) ==> target <= s[idx]
// @ ensures found == (idx < len(s) && s[idx] == target)
func BinarySearch(s []int, target int) (idx int, found bool) {
	if len(s) == 0 {
		return 0, false
	}
	low := 0
	high := len(s)
	mid := 0
	// @ invariant forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], 1/2)
	// @ invariant 0 <= low && low <= high && high <= len(s)
	// @ invariant 0 <= mid && mid < len(s)
	// @ invariant low > 0 ==> s[low-1] < target
	// @ invariant high < len(s) ==> target <= s[high]
	for low < high {
		// fmt.Println(low, high, s[:low], s[low:high], s[high:])
		mid = (low + high) / 2
		if s[mid] < target {
			low = mid + 1
		} else {
			high = mid
		}
	}
	// fmt.Println(low, high, s[:low], s[low:high], s[high:])
	return low, low < len(s) && s[low] == target
}

func client() {
	s := []int{0, 1, 1, 2, 3, 5, 8}
	i1, found1 := BinarySearch(s, 1)
	// @ assert found1 && s[i1] == 1 && i1 == 1
	i2, found2 := BinarySearch(s, 2)
	// @ assert found2 && s[i2] == 2 && i2 == 3
	i4, found4 := BinarySearch(s, 4)
	// @ assert !found4 && i4 == 5
	i10, found10 := BinarySearch(s, 10)
	// @ assert !found10 && i10 == len(s)
}
```
