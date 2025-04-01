# Wildcard permission

The permission amount `_` stands for an arbitrary positive permission amount.
Since the specific amount is unspecified, holding `acc(p, _)` enables reading but not writing.

By requiring `acc(p, _)`, we can make the method `sum` more versatile, allowing it to be called in cases where we have, for example only `acc(p, 1/4)` instead of `acc(p, 1/2)`:
``` go verifies
type pair struct {
	left, right int
}

// @ requires acc(p, _)
// @ ensures acc(p, _)
// @ ensures s == p.left + p.right
// @ ensures p.left == old(p.left) && p.right == old(p.right)
func (p *pair) sum() (s int) {
	return p.left + p.right
}

// @ requires acc(p1, 1/2)
// @ requires acc(p2, 1/4)
func client1(p1, p2 *pair) {
	p1.sum()
	p2.sum()
}
```
<!-- TODO: ensures acc(p, _) is unnecessary -->
However, this comes with the drawback that we cannot recover the exact permission amounts.
As seen in the following `client` code, where we lose write access, meaning `p.left` and `p.right` can no longer be modified.
The postcondition `acc(p, _)` ensures only that an unspecified positive permission amount is transferred back to the caller, but does not guarantee that it matches the unspecified positive permission amount that the caller initially transferred.
``` go does_not_verify
func client() {
	p := &pair{3, 5}
	res := p.sum()
	// @ assert p.left == 3 && p.right == 5
	p.left = p.right // Error
	p.right = res
	// @ assert p.left == 5 && p.right == 8
}
```
``` text
ERROR Assignment might fail. 
Permission to p.left might not suffice.
```
Please also note that, in order to frame the property
``` go
// @ assert p.left == 3 && p.right == 5
```
we have to include the following postcondition. From the perspective of the caller, an unspecified permission amount could also include write permission.
``` go
// @ ensures p.left == old(p.left) && p.right == old(p.right)
```
