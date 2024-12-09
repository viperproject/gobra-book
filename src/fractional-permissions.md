# Fractional Permissions

So far we have seen permissions of the form `acc(x)` for a pointer `x`.
We can be more specific and give a permission amount as the second argument to `acc`, as a fractional number.

- The amount `1` allows us to read and write
  `acc(x)`, or equivalently `acc(x, 1)`, `acc(x, writePerm)`, `acc(x, 1/1)`
- A positive amount `< 1` allows only reading (e.g. `acc(x, 1/2)`, `acc(x, 3/4)`)
- No access is denoted as `acc(x, 0)` or equivalently `acc(x, noPerm)`.
- A permission amount `> 1` is a contradiction and implies `false`.

Permission amounts to the same location can be summed, for example `acc(x, 3/4)` is equivalent to `acc(x, 1/4) && acc(x, 1/4) && acc(x, 1/4)`.
For concurrency this will be useful since it allows us to split read permissions to multiple threads and guaranteeing that there can only be one thread alive with (exclusive) write permission to a location [^1].
In the remainder of this section we study how to use fractional permissions with examples.

## Reading struct fields
Previously we saw the function `swap` that needs `write` access to both variables.
In the following example, we sum the fields `left` and `right` of a struct `pair`.
``` go
type pair struct {
	left, right int
}
//@ preserves acc(&p.left) && acc(&p.right)
//@ ensures s == p.left + p.right
//@ ensures p.left == old(p.left) && p.right == old(p.right)
func (p *pair) sum() (s int) {
	return p.left + p.right
}
func client() {
	p := &pair{3, 5}
	res := p.sum()
    //@ assert p.left == 3 && p.right == 5
	//@ assert res == 8
}
```
Note that we specify access to the struct fields as `acc(&p.left)` and not `acc(p.left)` as `p.left` is a value of type integer, but access is held to a resource (here pointer).

For the assertions to pass, we must specify that `sum` does not modify the fields of the pair.
Forgetting the second postcondition, functions like `dangerousSum` could satisfy this specification:
``` go
//@ preserves acc(&p.left) && acc(&p.right)
//@ ensures s == p.left + p.right
func (p *pair) dangerousSum() (s int) {
    p.left, p.right = 0, 0
	return 0
}
```

Let us simplify again.
If we require only read access, e.g. with the permission amount `1/2`,
we can leave out the second postcondition:
``` go
//@ preserves acc(&p.left, 1/2) && acc(&p.right, 1/2)
//@ ensures s == p.left + p.right
```

For a pointer `p` to a struct, we can additionally use the syntactic sugar `acc(p, 1/2)`,
which denotes permission of `1/2` to all fields of the struct.

Concretely for our example
`acc(&p.left, 1/2) && acc(&p.right, 1/2)`
can be replaced by `acc(p, 1/2)`

``` go
//@ preserves acc(p, 1/2)
//@ ensures s == p.left + p.right
func (p *pair) sum() (s int) {
	return p.left + p.right
}

func client() {
	p := &pair{3, 5}
	res := p.sum()
	//@ assert p.left == 3 && p.right == 5
	//@ assert res == 8
}
```


## Framing
If we change `client` to get only permission `1/2` from the precondition, Gobra reports an error.
``` go
//@ requires acc(p, 1/2)
//@ requires p.left == 0
func client(p *pair) {
	res := p.sum()
	//@ assert p.left == 0
}
```
``` text
Assert might fail. 
Assertion p.left == 0 might not hold.
```

The method `sum` requires `acc(p, 1/2)` which must be transferred by the caller.
We would like to *frame* the property `p.left == 0` across the call.
For this, the caller must retain a non-negative permission which prevents write access.

One way to frame the property is to require a higher permission amount like `3/4`.
Then `client` keeps `acc(p, 1/4)` across the call and we are sure that `p.left` is not modified.
``` go
//@ requires acc(p, 3/4)
//@ requires p.left == 0
func client(p *pair) {
	res := p.sum()
	//@ assert p.left == 0
}
```

## Pointers revisited
For a pointer `x`, for any positive permission amount `p`, `acc(x, p)` implies `x != nil`.
But `acc(x1, 1/2) && acc(x2, 1/2)` does no longer imply `x1 != x2`.
If we have `2/3` fractional permission to `x1` instead, we can now infer `x1 != x2` 
since permission amounts to the same location are added together (`x1 == x2 ==> acc(x1, 7/6)`):
``` gobra
requires acc(x1, 2/3) && acc(x2, 1/2)
ensures x1 != x2
func lemma(x1, x2 *int) {}
```

## `inhale` and `exhale`
Permissions can be manually added (removed) by inhaling (exhaling).
This can be useful for debugging but should not be needed for normal verification purposes.

The statement `exhale ASSERTION`
1. asserts that all value constraints in `ASSERTION` hold
2. asserts that all permissions mentioned by `ASSERTION` are held
3. removes all permissions mentioned by `ASSERTION`

Exhale is similar to `assert`, with the difference that `assert` does not remove any permissions:
``` gobra
requires acc(x, 1)
func breathingTraining(x *int) {
	assert acc(x, 1)
	exhale acc(x, 1/4)
	assert acc(x, 3/4)
	assert acc(x, 3/4)
}
```

The statement `inhale ASSERTION`
1. adds all permissions mentioned by `ASSERTION`
2. assumes all value constraints in `ASSERTION` hold


## Access Predicates are not duplicable
In classical logic, if the proposition \\( P \\) holds then clearly the proposition \\( P \land P\\) holds as well.
For assertions containing access predicates, this does no longer hold.
Consider `acc(p, 1/2)` which denotes read permission.
But `acc(p, 1/2) && acc(p, 1/2)` implies full permissions `acc(p, 1)`.


## Footnotes
[^1]: As a simple illustration; for more please refer to the chapter on concurrency.
``` go
//@ requires acc(p, 1/2)
func reader(p *int) {
	_ = *p
	// ...
}

//@ requires acc(p, 1)
func driver(p *int) {
	go reader(p)
	go reader(p)
}
```
