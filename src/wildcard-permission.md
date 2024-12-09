# Wildcard Permission

The wildcard permission `_` that stands for an arbitrary positive permission amount (e.g. `acc(p, _)`).
It enables reading but not writing.

For example, we could make `sum` more versatile and allow it to be called in cases where we have only `acc(p, 1/4)` instead of `acc(p, 1/2)`.
``` go
~type pair struct {
~	left, right int
~}
//@ requires acc(p, _)
//@ ensures acc(p, _)
//@ ensures s == p.left + p.right
//@ ensures p.left == old(p.left) && p.right == old(p.right)
func (p *pair) sum() (s int) {
	return p.left + p.right
}
func client() {
	p := &pair{3, 5}
	res := p.sum()
	//@ assert p.left == 3 && p.right == 5
	p.left, p.right = p.right, res	// Error
	//@ assert p.left == 5 && p.right == 8
}
```
``` text
Assignment might fail. 
Permission to p.left might not suffice.
```
With the drawback that `client` cannot recover the exact permission amount and can no longer write `p.left` and `p.right`.
The postcondition `acc(p, _)` ensures only that an unspecified positive permission amount is transferred back to the caller but does not guarantee that it is equal to the unspecified positive permission amount that the caller initially transferred.

