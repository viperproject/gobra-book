# Self-Framing Assertions

Assertions must be well-defined and require access to all locations being read.

If we forget to transfer permissions back, the postcondition has no permission to read `*y` and `*x`.
``` go
//@ requires acc(x) && acc(y)
//@ ensures *x == old(*y) && *y == old(*x)
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

We can make it self-framing:
``` go
//@ requires acc(x) && acc(y)
//@ ensures acc(x) && acc(y)
//@ ensures *x == old(*y) && *y == old(*x)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
```

The order of pre/postconditions matters.
When we exchange the postconditions we get the same error:
``` go
//@ requires acc(x) && acc(y)
//@ ensures *x == old(*y) && *y == old(*x)
//@ ensures acc(x) && acc(y)
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