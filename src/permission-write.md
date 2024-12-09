# Permission to write

Permissions allow us to reason about mutable data.
Reading and writing to a location is permitted based on the permission amount held.
Permissions can be transferred between functions/methods, loop iterations, and are gained on allocation.

This is crucial for concurrency, as a short teaser, Gobra can reject the following program with a data race:
``` go
func inc(p *int) {
	*p = *p + 1
}

func driver(p *int) {
	go inc(p)
	go inc(p)
}
```

Permissions are held to *resources*.
The following chapter will also introduce access to predicates but for now, we are concerned only with pointers.


For a pointer to an integer `x *int`,
the accessibility predicate `acc(x)` denotes write (and read) access to `x`.

Having access `acc(x)` to a pointer `x` implies `x != nil` and that reading (e.g. `tmp := *x`) and writing (e.g. `*x = 1`) does not panic.

Let us illustrate this with a function that swaps the values of two integer pointers:
``` go
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
```
Go provides memory safety and does not try to access invalid memory.
Similar to out-of-bounds array indices, a runtime error occurs when we call `swap(nil, x)`:
``` text
panic: runtime error: invalid memory address or nil pointer dereference
[signal SIGSEGV: segmentation violation code=0x1 addr=0x0 pc=0x466c23]

goroutine 1 [running]:
main.swap(...)
        /gobra/swap.go:8
main.main()
        /gobra/swap.go:14 +0x3
exit status 2
```
Gobra can detect this statically.
Without access yet, we get the error:
``` text
Assignment might fail. 
Permission to *x might not suffice.
```
The permissions a function requires must be specified in the precondition.
Since `swap` modifies both `x` and `y` we write:
``` go
//@ requires acc(x) && acc(y)
func swap(x *int, y *int) {
~	tmp := *x
~	*x = *y
~	*y = tmp
}
```

If we now try to swap,
``` go
func client() {
	a := 1
	b := 2
    x := &a
    y := &b
	swap(x, y)
}
```
we first get the error:
``` text
property error: got a that is not effective addressable
        x := &a
      ^
```
Gobra requires us to be explicit and mark a variable `a` that is referenced with `a /*@@@*/`.
This should ensure that the programmer is aware, in which cases, Gobra employs the *permission machinery*.
Otherwise, if the local variables `a` and `b` are never referenced, reasoning about them is much easier.
Note that the outer `@`s belong to the annotation, so the equivalent in Gobra is just `a@`.
``` go
~func client() {
	a /*@@@*/ := 1
	b /*@@@*/ := 2
    x := &a
    y := &b
	swap(x, y)
	//@ assert *x == 2
	//@ assert *y == 1
}
```

In our example, permissions `acc(x)` and `acc(y)` are obtained in `client` when initializing `x` and `y`,
then transferred when calling `swap(x, y)`.
We add the postcondition `acc(x) && acc(y)` to transfer the permissions back to the caller when the function returns.
Otherwise the permissions are leaked (lost).

With `old(*y)` we can use the value of `*y` from the state at the beginning of the function call before any modifications.
``` go
//@ requires acc(x) && acc(y)
//@ ensures acc(x) && acc(y)
//@ ensures *x == old(*y) && *y == old(*x)
func swap(x *int, y *int) {
	~tmp := *x
	~*x = *y
	~*y = tmp
}
```

## Aliasing
Clients may want to call `swap` with the same argument `swap(x, x)`.
So far, our specification forbids this and we get the error:
``` go
Precondition of call swap(x, x) might not hold. 
Permission to y might not suffice.
```
Having `acc(x) && acc(y)` implies `x != y` since we are not allowed to have write access to the same location.

One possibility is to perform a case distinction on `x == y`.
While this works, the resulting specs are verbose, and we better refactor them to a reduced form.
``` go
//@ requires x == y ==> acc(x)
//@ requires x != y ==> acc(x) && acc(y)
//@ ensures x == y ==> acc(x)
//@ ensures x != y ==> acc(x) && acc(y)
//@ ensures x != y ==> *x == old(*y) && *y == old(*x)
//@ ensures x == y ==> *x == old(*x)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
```

1. It is a common pattern that a function requires and ensures the same permissions. Here we have
    ``` go
    //@ requires x == y ==> acc(x)
    //@ ensures x == y ==> acc(x)
    ```
    We can replace this with a single line using `preserves`, which is syntactical sugar for the above.
    ``` go
    //@ preserves x == y ==> acc(x)
    ```
2. `acc(x)` is needed in any case, hence it can be factored out
    ``` go
    //@ preserves x == y ==> acc(x)
    //@ preserves x != y ==> acc(x) && acc(y)
    ```
    becomes
    ``` go
    //@ preserves acc(x)
    //@ preserves x != y ==> acc(y)
    ```
3. Simplify the postconditions
    ``` go
    //@ ensures x != y ==> *x == old(*y) && *y == old(*x)
    //@ ensures x == y ==> *x == old(*x)
    ```
    with:
    ``` go
    //@ ensures *x == old(*y) && *y == old(*x)
    ```
    where the assertion is unchanged for the case `x != y` and we see it is equivalent for the case `x == y` by substituting `y` with `x`.


We have simplified the specification significantly and the client can now use swap also in cases where `x` and `y` are aliases.
This gives us the...

## Final Version of `swap`
``` go
//@ preserves acc(x)
//@ preserves x != y ==> acc(y)
//@ ensures *x == old(*y) && *y == old(*x)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
func client() {
	a /*@@@*/ := 1
	b /*@@@*/ := 2
	x := &a
	y := &b
	swap(x, x)
	//@ assert *x == 1
	swap(x, y)
	//@ assert *x == 2
	//@ assert *y == 1
}
```

