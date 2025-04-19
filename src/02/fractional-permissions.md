# Permission to read

So far, we have seen permissions of the form `acc(x)` for a pointer `x`.
We can be more specific and give a permission amount as the second argument to `acc`, as a fractional number.
In this case, we speak of _fractional permissions_:
- A permission amount of `1` allows us to read and write (e.g., `acc(x, 1)`, or equivalently `acc(x)`, `acc(x, writePerm)`, `acc(x, 1/1)`)
- A positive amount `< 1` allows only reading (e.g. `acc(x, 1/2)`, `acc(x, 3/4)`)
- No access is denoted as `acc(x, 0)` or equivalently `acc(x, noPerm)`.
- A permission amount `> 1` for a pointer is a contradiction and implies `false`. 

If a function requires write permission, and yet we want to guarantee that the value stored at the locations remains unchanged, an extra postcondition must be added.
Requiring only read permission, a caller retaining a positive permission amount can guarantee across the call that the value remained unchanged.

Permission amounts to the same location can be split up, for example, `acc(x, 3/4)` is equivalent to `acc(x, 1/4) && acc(x, 1/4) && acc(x, 1/4)`.

In the remainder of this section, we study how to use fractional permissions with examples.

Previously, we saw the function `swap` that needs `write` access to both variables.
In the following example, we sum the fields `left` and `right` of a struct `pair`.
Since we only read the fields, we specify a permission amount of `1/2`.
``` go verifies
type pair struct {
	left, right int
}

// @ preserves acc(&p.left, 1/2) && acc(&p.right, 1/2)
// @ ensures s == p.left + p.right
func (p *pair) sum() (s int) {
	return p.left + p.right
}

func client() {
	p := &pair{3, 5}
	res := p.sum()
	// @ assert p.left == 3 && p.right == 5
	// @ assert res == 8
}
```

Note that we specify access to the struct fields as `acc(&p.left)` and not `acc(p.left)` as `p.left` is a value of type integer, but access is held to a resource (in this case, a pointer).
For a pointer `p` to a struct, we can additionally use the syntactic sugar `acc(p, 1/2)`,
which denotes permission of `1/2` to all fields of the struct.
Concretely, we can replace in our example
``` go
// @ preserves acc(&p.left, 1/2) && acc(&p.right, 1/2)`
```
with
``` go
// @ preserves acc(p, 1/2)
```

## Framing properties
<!-- Forgetting the second postcondition, functions like `dangerousSum` could satisfy this specification: -->
<!-- ``` go -->
<!-- // @ preserves acc(&p.left) && acc(&p.right) -->
<!-- // @ ensures s == p.left + p.right -->
<!-- func (p *pair) dangerousSum() (s int) { -->
<!--     p.left, p.right = 0, 0 -->
<!-- 	return 0 -->
<!-- } -->
<!-- ``` -->

Since `sum` requires only `acc(p, 1/2)`, and client acquires full access on allocation,
we can _frame_ the property `p.left == 3 && p.right == 5` across the call `p.sum()`, without specifying that the shared struct is not modified.
``` go verifies
// @ preserves acc(p, 1/2)
// @ ensures s == p.left + p.right
func (p *pair) sum() (s int) {
	return p.left + p.right
}

func client() {
	p := &pair{3, 5}
	res := p.sum()
	// @ assert p.left == 3 && p.right == 5
	// @ assert res == 8
}
```
But if we change `client` to get only permission amount `1/2` for `p`, Gobra reports an error.
``` go does_not_verify
// @ requires acc(p, 1/2)
// @ requires p.left == 0
func client2(p *pair) {
	res := p.sum()
	// @ assert p.left == 0
}
```
``` text
Assert might fail. 
Assertion p.left == 0 might not hold.
```

The method `sum` requires `acc(p, 1/2)`, which must be transferred from the caller.
To frame the property `p.left == 0` across the call, the caller must retain a non-negative permission amount to prevent write access.
One way is to require a higher permission amount like `3/4`.
Then, `client` keeps `acc(p, 1/4)` across the call, and we are sure that `p.left` is not modified.
``` go
// @ requires acc(p, 3/4)
// @ requires p.left == 0
func client3(p *pair) {
	res := p.sum()
	// @ assert p.left == 0
}
```

Now let us consider `sum` with a different contract, where write access is required:
``` go verifies
type pair struct {
	left, right int
}

// @ preserves acc(&p.left, 1) && acc(&p.right, 1)
// @ ensures s == p.left + p.right
// @ ensures p.left == old(p.left) && p.right == old(p.right)
func (p *pair) sum() (s int) {
	return p.left + p.right
}

func client() {
	p := &pair{3, 5}
	res := p.sum()
	// @ assert p.left == 3 && p.right == 5
	// @ assert res == 8
}
```
For the assertions in `client` to pass, we specify that `sum` does not modify the fields of the pair
with the postcondition `p.left == old(p.left) && p.right == old(p.right)`.

## Fractional permissions and pointers
For a pointer `x`, for any positive permission amount `p`, `acc(x, p)` implies `x != nil`.
But `acc(x1, 1/2) && acc(x2, 1/2)` does no longer imply `x1 != x2`.
If we have `2/3` fractional permission to `x1` instead, we can now infer `x1 != x2` 
since permission amounts to the same location are added together:
``` go verifies
// @ requires acc(x1, 2/3) && acc(x2, 1/2)
// @ ensures x1 != x2
func fact(x1, x2 *int) {}
```

## Access predicates are not duplicable
In classical logic, if the proposition \\( P \\) holds, then clearly, the proposition \\( P \land P\\) holds as well.
For assertions containing access predicates, this no longer holds.
Consider `acc(p, 1/2)`, which denotes read permission, and `acc(p, 1/2) && acc(p, 1/2)`, which implies write permission `acc(p, 1)`.

