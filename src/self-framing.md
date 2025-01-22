# Self-framing assertions

Assertions in Gobra must be _well-defined_.
This includes the fact that array indices in specifications must be in bounds.
Operations like division have conditions under which they are well-defined.
For `a / b` to be well-defined, `b != 0` must hold.
In the context of permissions, we get a new requirement that assertions are _self-framing_,
i.e. access to all locations being read is required.
Gobra checks that assertions are self-framing, and reports an error otherwise.

This also applies to contracts.
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

We can make it _self-framing_ by returning the permissions `acc(x)` and `acc(y)`:
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


Note that the order of the pre- and postconditions matters.
The contract is checked from top to bottom and permission must be held before accessing.
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
As a result, 
``` gobra
ensures acc(x) && acc(y) && *x == old(*y)
```
is self-framing, while the following is not:
``` gobra
ensures *x == old(*y) && acc(x) && acc(y)
```

As an exception, the assertion from an `assert` statement must not be self-framing.
For example, we can write `*x == 1` instead of `acc(x) && *x == 1`.
However, Gobra reports an error if `acc(x)` is not held in the state.
``` go
func client() {
	x := new(int)
    *x = 1
    // @ assert *x == 1
    // @ assert acc(x) && *x == 1
}
```



> Well-defined assertions that require access to all locations being read are called _self-framing_.
> Gobra checks that assertions are self-framing, and reports an error otherwise.
