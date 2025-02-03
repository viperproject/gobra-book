# Permission type and parameter

Having a fixed permission amount in the contract is restrictive.
For example, clients with only `acc(r, 1/4)` cannot call `p.sum()`:
``` go
type pair struct {
	left, right int
}

// @ requires acc(p, 1/2)
// @ ensures acc(p, 1/2)
// @ ensures s == p.left + p.right
func (p *pair) sum() (s int) {
	return p.left + p.right
}

// @ requires acc(p, 1/4)
// @ requires p.left == 2 && p.right == 3
func client(p *pair) {
	res := p.sum()
	// @ assert res == 5
}
```
``` text
ERROR Precondition of call p.sum() might not hold. 
Permission to p might not suffice.
```

One option is to use the [wildcard permission](./wildcard-permission.md) amount, as previously studied, which comes with its own drawbacks.
In this section, we show how to abstract the exact permission amount by introducing a ghost parameter of type `perm`, i.e. Gobra's type for permission amounts:
``` go
type pair struct {
	left, right int
}

// @ requires a > 0	    // <--- added
// @ requires acc(p, a) // <--- changed
// @ ensures acc(p, a)	// <--- changed
// @ ensures s == p.left + p.right
func (p *pair) sum( /*@ ghost a perm @*/ ) (s int) { // <--- new parameter
	return p.left + p.right
}

// @ requires acc(p, 1/2)
// @ requires p.left == 2 && p.right == 3
func client(p *pair) {
	res := p.sum( /*@ 1/4 @*/ )  // <--- changed
	// @ assert res == 5
}
```
Conventionally the permission amount is called `p`, which clashes here with our `pair` pointer.
When calling `sum`, we must pass the permission amount: `p.sum( /*@ 1/4 @*/ )`.
The precondition `p > 0` is important to get read permission, otherwise we get:
``` text
ERROR Method contract is not well-formed.
Expression p might be negative.
```


## Permission arithmetic
We may convert a fraction to a permission amount and perform calculations with it: 
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
Note that for access predicates, we can, and have been using the shorthand `acc(p, 1/2)` instead of `acc(p, perm(1/2))`.
