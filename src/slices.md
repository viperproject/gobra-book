# Slices

Slices provide a useful abstraction to a access a contiguous sequence of data.
A slice has a length, a capacity and use an underlying array as storage.

In the following example, a constant `n` is added to a slice.
The functions `len` and `cap` can be used in contracts.
Access to slice elements is specified using quantified permissions.
Note that the loop must preserve the permissions with an invariant.
``` go
// @ preserves forall k int :: {&s[k]} 0 <= k && k < len(s) ==> acc(&s[k])
// @ ensures forall k int :: {&s[k]} 0 <= k && k < len(s) ==> s[k] == old(s[k]) + n
func addToSlice(s []int, n int) {
	//@ invariant 0 <= i && i <= len(s)
	//@ invariant forall k int :: {&s[k]} 0 <= k && k < len(s) ==> acc(&s[k])
	//@ invariant forall k int :: {&s[k]} i <= k && k < len(s) ==> s[k] == old(s[k])
	//@ invariant forall k int :: {&s[k]} 0 <= k && k < i ==> s[k] == old(s[k]) + n
	for i := 0; i < len(s); i += 1 {
		s[i] = s[i] + n
	}
}

func client() {
	s := make([]int, 4, 8)
	//@ assert len(s) == 4 && cap(s) == 8
	addToSlice(s, 1)
	//@ assert forall i int :: {&s[i]} 0 <= i && i < 4 ==> s[i] == 1
}
```
In the above example, we obtain permission to the slice elements on allocation by making them.
We obtain permission to the slice elements on allocation,
in the above example by making it.
``` go
s1 := []int{0, 1, 1, 2, 3, 5}
//@ assert forall i int :: {&s1[i]} 0 <= i && i < len(s1) ==> acc(&s1[i])
//@ assert acc(s1)
```
After initialization with a literal, we also gain permission.
The second assertion is syntactic sugar for the first.
## Slicing
A slice can be created from another slice or array by slicing it, in general with an expression of the form `a[i:j:k]`.
To avoid panics, as part of the contract of the slicing operation, Gobra checks that `0 <= i && i <= j && j <= k && k <= cap(a)`.

We can create two overlapping slices `l` and `r` but run into a permission error:
``` go
~func client2() {
    s := make([]int, 3)
    l := s[:2]
    r := s[1:]
    addToSlice(l, 1)
    addToSlice(r, 1)
~}
```
``` go
ERROR Assert might fail. 
Permission to r might not suffice.
```
While we should not be able to assert `acc(l) && acc(r)` (why?),
to call `addToSlice` we only need permission for either of the slices.
In order to get permission for the slice `r` we must explicitly assert how the addresses to the elements of `r` relate to those of `s`.
``` go
func client2() {
	s := make([]int, 3)
	l := s[:2]
	r := s[1:]
	//@ assert forall i int :: {&r[i]} 0 <= i && i < len(r) ==> &r[i] == &s[i+1]
	addToSlice(l, 1)
	//@ assert s[0] == 1 && s[1] == 1
	addToSlice(r, 1)
	//@ assert r[0] == 2 && r[1] == 1
	//@ assert s[0] == 1 && s[1] == 2 && s[2] == 1
}
```

## Copy and Append
Go includes the `copy` and `append` built-in functions for common slice operations.

We give the contracts for `copy` and `append` for a generic type `T` (Gobra does not yet support generics).
In Gobra we must pass an additional ghost parameter for the permission amount required to read the elements of `src`.
This allows the functions generally to be used independent of the exact permission amount.
``` gobra
requires p > 0
requires forall i int :: { &src[i] } 0 <= i && i < len(src) ==> acc(&src[i])
requires forall i int :: { &xs[i] } 0 <= i && i < len(xs) ==> acc(&xs[i], p)
ensures len(res) == len(src) + len(xs)
ensures forall i int :: { &res[i] } 0 <= i && i < len(res) ==> acc(&res[i])
ensures forall i int :: { &xs[i] } 0 <= i && i < len(xs) ==> acc(&xs[i], p)
ensures forall i int :: { &res[i] } 0 <= i && i < len(src) ==> res[i] === old(src[i])
ensures forall i int :: { &res[i] } len(src) <= i && i < len(res) ==> res[i] === xs[i - len(src)]
func append[T any](ghost p perm, src []T, xs ...T) (res []T)
```

Note that since `append` is variadic, the permission must be the first argument.
The permission to `src` is lost as the underlying array could be reallocated if the capacity is not sufficient to append the new elements.
`s = append(s, 42)` is a common pattern in Go and this way permissions to `s` are preserved.

`copy` copies the elements from `src` to `dst`, stops when the end of the shorter slice is reached and returns the number of elements copied.
 ``` gobra
requires 0 < p
requires forall i int :: { &dst[i] } (0 <= i && i < len(dst)) ==> acc(&dst[i], write)
requires forall i int :: { &src[i] } (0 <= i && i < len(src)) ==> acc(&src[i], p)
ensures len(dst) <= len(src) ==> res == len(dst)
ensures len(src) < len(dst) ==> res == len(src)
ensures forall i int :: { &dst[i] } 0 <= i && i < len(dst) ==> acc(&dst[i], write)
ensures forall i int :: { &src[i] } 0 <= i && i < len(src) ==> acc(&src[i], p)
ensures forall i int :: { &dst[i] } (0 <= i && i < len(src) && i < len(dst)) ==> dst[i] === old(src[i])
ensures forall i int :: { &dst[i] } (len(src) <= i && i < len(dst)) ==> dst[i] === old(dst[i])
func copy[T any](dst, src []T, ghost p perm) (res int)
 ```

Permissions must be explicitly passed as `perm(1/2)` instead of only `1/2` as is allowed in the access predicate.
This simple example shows the usage of `copy` and `append`:
``` go
s1 := []int{1, 2}
s2 := []int{3, 4, 5}
                                                                         
s0 := make([]int, len(s1))
copy(s0, s1 /*@, perm(1/2) @*/)
//@ assert forall i int :: {&s0[i]} {&s1[i]} 0 <= i && i < len(s0) ==> s0[i] == s1[i]
                                                                         
s3 := append( /*@ perm(1/2), @*/ s1, s2...)
s4 := append( /*@ perm(1/2), @*/ s0, 3, 4, 5)
//@ assert forall i int :: {&s3[i]} {&s4[i]} 0 <= i && i < len(s3) ==> s3[i] == s4[i]
```

Using the nil slice we could refactor the `make` and `copy` to the single line `s0 := append([]int(nil), s1...)` .
As opposed to the nil pointer, we can have permission to the nil slice:
``` go
var s2 []int
//@ assert acc(s2)
//@ assert s2 == nil && len(s2) == 0 && cap(s2) == 0
```

In Go it is possible to append a slice to itself.
The contract of `append` forbids this.
``` go
s1 := []int{1, 2}
s2 := append( /*@ perm(1/64), @*/ s1, s1...)
```
``` text
ERROR Precondition of call append(  perm(1/64),  s1, s1...) might not hold. 
Permission to append(  perm(1/64),  s1, s2...) might not suffice
```

Similarly, in Go the behavior of `copy` is independent whether the underlying memory of the slices overlaps.
Again, Gobra's contract of `copy` forbids this:
``` go
s := []int{1, 2, 3, 4}
s1 := s[1:]
//@ assert acc(s1)
copy(s, s1 /*@, perm(1/2) @*/)
// fmt.Println(s) // [2 3 4 4]
```
``` text
ERROR Precondition of call copy(s, s1 , perm(1/2) ) might not hold. 
Permission to copy(s0, s1 , perm(1/2) ) might not suffice.
```

## TODO Range
<!-- WAIT question: can't modify ? -->
``` go
// @ requires len(s) > 0
// @ preserves acc(s)
// @ ensures forall k int :: {&s[k]} 0 <= k && k < len(s) ==> s[k] == old(s[k]) + n
func addToSlice(s []int, n int) {
	//@ invariant acc(s)
	//@ invariant forall k int :: {&s[k]} i0 <= k && k < len(s) ==> s[k] == old(s[k])
	//@ invariant forall k int :: {&s[k]} 0 <= k && k < i0 ==> s[k] == old(s[k]) + n
	for i, e := range s /*@ with i0 @*/ {
		s[i] = e + n
	}
}
```
<!-- TODO chose one example -->
``` go
// @ requires len(s) > 0
// @ preserves acc(s, 1/2)
// @ ensures forall j int :: {&s[j]} 0 <= j && j < len(s) ==> res >= s[j]
// @ ensures 0 <= idx && idx < len(s) && s[idx] == res
func sliceMax(s []int) (res int /*@ , ghost idx int @*/) {
	res = s[0]
	//@ invariant acc(s, 1/2)
	//@ invariant forall j int :: {&s[j]} 0 <= j && j < i0 ==> res >= s[j]
	//@ invariant 0 <= idx && idx < len(s) && s[idx] == res
	for i, a := range s /*@ with i0 @*/ {
		if a > res {
			res = a
			//@ idx = i
		}
	}
	return
}

func client() {
	s := make([]int, 10, 15)
	//@ assert len(s) == 10 && cap(s) == 15
	m /*@, idx @*/ := sliceMax(s)
	//@ assert m == 0
	s[len(s)-1] = 5
	m /*@, idx @*/ = sliceMax(s)
	//@ assert m == 5
}
```

### Wildcard and Range
As a consequence, the wildcard permission does not suffice to iterate over the range.
``` go
// @ requires acc(s, _)
func wildRange(s []int) {
	for i, e := range s {}
}
```
``` text
Might not have read permission to range expression.
Permission to s might not suffice.
```

## Binary Search Example
We conclude this section by returning to the binary search example,
giving a version for slices with the difference that `binarySearch` returns whether the element `value` is found in the array and not the index where it would have been inserted.
Now we can handle slices of arbitrary length and have a more efficient implementation, with the drawback of having to specify permissions.

``` go
~/*@
~ghost
~requires forall i int :: {&s[i]} 0 <= i && i < len(s) ==> acc(&s[i], 1/2)
~decreases
~pure func isSliceSorted(s []int) bool {
	~return forall i, j int :: {&s[i], &s[j]} 0 <= i && i < j && j < len(s) ==> s[i] <= s[j]
~}
~@*/

// @ preserves acc(s, 1/2)
// @ preserves isSliceSorted(s)
// @ ensures forall i int :: {&s[i]} 0 <= i && i < len(s) ==> old(s[i]) == s[i]
// @ ensures found ==> 0 <= idx && idx < len(s) && s[idx] == value
// @ ensures !found ==> forall i int :: {&s[i]} 0 <= i && i < len(s) ==> s[i] != value
func binarySearch(s []int, value int) (found bool /*@ , ghost idx int @*/) {
	if len(s) == 0 {
		return false /*@ , -1 @*/
	}
	low := 0
	high := len(s) - 1
	mid := 0
	// @ invariant acc(s, 1/2)
	// @ invariant 0 <= low && low <= high && high < len(s)
	// @ invariant 0 <= mid && mid < len(s)
	// @ invariant forall i int :: {&s[i]} 0 <= i && i < len(s) ==> old(s[i]) == s[i]
	// @ invariant forall i int :: {&s[i]} 0 <= i && i < low ==> s[i] < value
	// @ invariant forall i int :: {&s[i]} high < i && i < len(s) ==>  value < s[i]
	for low < high {
		mid = (low + high) / 2
		if s[mid] == value {
			return true /*@, mid @*/
		} else if s[mid] < value {
			low = mid + 1
		} else {
			high = mid
		}
	}
	return s[low] == value /*@ , low @*/
}

func binarySearchClient() {
	xs := []int{1, 5, 7, 11, 23, 43, 53, 123, 234, 1024}

	found /*@, idx @*/ := binarySearch(xs, 11)
	//@ assert found ==> xs[idx] == 11
	//@ assert !found ==> forall i int :: {&xs[i]} 0 <= i && i < len(xs) ==> xs[i] != 11

	found /*@, idx @*/ = binarySearch(xs, 12)
	//@ assert !found
}
```
