# Self-framing assertions

Assertions in Gobra must be _well-defined_.
This includes the fact that [array indices](./basic-array.md) in specifications must be in bounds.
Operations like division have conditions under which they are well-defined.
For `a / b` to be well-defined, `b != 0` must hold.
In the context of permissions, we get a new requirement:

> Well-defined assertions that require access to all locations being read are called _self-framing_.
> Gobra checks that assertions are self-framing, and reports an error otherwise.

This applies also to contracts.
In the following example, there is an error since `*x` and `*y` are accessed in the postcondition of `swap`,
without holding permissions for `x` and `y`:
``` go
// @ requires acc(x) && acc(y)
// @ ensures *x == old(*y) && *y == old(*x)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
```
``` text
ERROR Method contract is not well-formed. 
Permission to *x might not suffice.
```

We can make it _self-framing_ by returning the permission `acc(x)` and `acc(y)`:
``` go
// @ requires acc(x) && acc(y)
// @ ensures acc(x) && acc(x)   // <------ added
// @ ensures *x == old(*y) && *y == old(*x)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
```


Note that the order of the pre and postconditions matters.
The contract is checked from top to bottom and permission must be held before an access.
For example, if we exchange the postconditions of `swap`, we get the same error again:
``` go
// @ requires acc(x) && acc(y)
// @ ensures *x == old(*y) && *y == old(*x)
// @ ensures acc(x) && acc(y)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
```
``` text
ERROR Method contract is not well-formed. 
Permission to *x might not suffice.
```

Conjunctions are evaluated from left to right.
Therefore the assertion `acc(x) && acc(y) && *x==old(*y)` is self-framing.

