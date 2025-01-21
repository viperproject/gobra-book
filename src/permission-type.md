# Permission type and parameter

The type for permissions in Gobra is `perm`.
We can convert a fraction to a permission and do calculations with it: 
``` gobra
func main() {
	assert perm(1/2) + perm(1/2) == writePerm
	assert perm(1) - 1/2 == perm(1/2)
	assert perm(1/2) * 0 == noPerm
	assert perm(1) / 2 != writePerm
	assert perm(1/3) == 1/3
	assert perm(perm(1/3)) == perm(1/3)
}
```

Note that for access predicates we can and have been using the shorthand `acc(r, 1/2)` instead of `acc(r, perm(1/2))`.
``` go
// Adapted from https://gobyexample.com/methods (CC BY 3.0)
type rect struct {
	width, height int
}
// @ preserves acc(r, 1/2)
// @ ensures a == r.width * r.height
func (r *rect) area() (a int) {
	return r.width * r.height
}

func main() {
	r/*@@@*/ := rect{width: 10, height: 5}
	a1 := r.area()
	assert a1 == 50
	rp := &r
	a2 := rp.area()
	assert a2 == 50
}
```

Having a fixed permission amount in the contract is restrictive.
For example clients with only `acc(r, 1/4)` cannot call `r.area()`.
We can abstract the exact permission amount by introducing a ghost parameter of type `perm`:
``` go
~package main
~type rect struct {
	~width, height int
~}
// @ requires p > 0
// @ preserves acc(r, p)
// @ ensures a == r.width * r.height
func (r *rect) area(/*@ghost p perm @*/) (a int) {
	return r.width * r.height
}

// @ requires acc(r, 1/4)
// @ requires r.width == 0
func client(r *rect) {
	// a1 := r.area()
	a1 := r.area(/*@1/8@*/)
	// @ assert a1 == 0
}
```

The precondition `p > 0` is important, otherwise we get:
``` text
ERROR Method contract is not well-formed.
Expression p might be negative.
```
