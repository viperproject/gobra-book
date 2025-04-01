# Permission to write

Permissions allow us to reason about aliased data in a modular way.
Reading from and writing to a location is permitted based on the permission amount held.
Write access is _exclusive_, i.e. permission to write to a location can only be held once.
Permissions can be transferred between functions/methods, loop iterations, and they are gained on allocation.

Consider the following program.
Should the assertion `snapshotX == *x` pass?
``` go
{{#include frame.go:inc}}
{{#include frame.go:client}}
```
If `x` and `y` were aliases, `*x` might be modified.
Even if they are not aliases, we could not exclude the possibility that `*x` could somehow get modified since the body of `inc` is unknown when modularly verifying `client`.

Therefore it is important that the contract of a function specifies what might be modified by this function.
In particular, this tells us what does not change without us having to explicitly specify it.
Given `x != y` and that `inc(y)` might only modify `*y`, the assertion `snapshotX == *x` shall hold before and after the call `inc(y)`.

So far, the program is rejected by Gobra:
``` text
ERROR Assignment might fail. 
Permission to *x might not suffice.
```
``` text
ERROR Assignment might fail. 
Permission to *p might not suffice.
```
In order to read and write the value stored at the memory address `x`, we must hold full access to this location.
This is denoted by the accessibility predicate `acc(x)`.
``` go verifies
{{#include frame.go:inc_full}}
{{#include frame.go:client_full}}
```
<!-- TODO which problem https://en.wikipedia.org/wiki/Frame_problem -->
Permissions are a solution to the problem described above.
Now `inc` requires `acc(p)`, which gives us an upper bound on what could be modified after the call.
In the function `client`, the permissions `acc(x)` and `acc(y)` are held from the precondition.
`acc(y)` is transferred when calling `inc(y)`.
Because `acc(x)` is kept, and write permission is exclusive, we can _frame_ the condition `snapshotX == *x` holds across the call `inc(y)`.

<!-- - As write permission is exclusive, the case where `x` and `y` are aliases is -->
<!-- e.g. with *x = y , and alternative body: **p += 1; *p+=1 -->

## Permission for pointers
<!-- The following chapter will also introduce access to predicates but for now, we are concerned only with pointers. -->
Permissions are held for _resources_.
For now, we only consider pointers.
Having access `acc(x)` to a pointer `x` implies `x != nil`, so reading (e.g. `tmp := *x`) and writing (e.g. `*x = 1`) do not panic.
Let us illustrate this with a function that swaps the values of two integer pointers:
``` go panics
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
```
Go provides memory safety and prevents access to invalid memory.
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
Gobra detects this statically.
Without holding access yet, we get the error:
``` text
Assignment might fail. 
Permission to *x might not suffice.
```
The permissions a function requires must be specified in the precondition.
Since `swap` modifies both `x` and `y`, we write:
``` go does_not_verify
// @ requires acc(x) && acc(y)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}

func client() {
	x := new(int)
	y := new(int)
	// @ assert acc(x)
	// @ assert acc(y)
	*x = 1
	*y = 2
	swap(x, y)
	// @ assert *x == 2 // error
	// @ assert *y == 1
}
```
``` text
ERROR Assert might fail. 
Permission to *x might not suffice.
```

In our example, permissions `acc(x)` and `acc(y)` are obtained in `client` when they are allocated with `new`,
then transferred when calling `swap(x, y)`.
With `assert acc(x)`, we can check whether the permission is held.
We add the postcondition `acc(x) && acc(y)` to transfer the permissions back to the caller when the function returns.
Otherwise the permissions are leaked (lost).

## `old` state
To specify the behavior of `swap`, we have to refer to the values `*x` and `*y` before any modifications.
With `old(*y)`, we can use the value of `*y` from the state at the beginning of the function call.
``` go verifies
// @ requires acc(x) && acc(y)
// @ ensures acc(x) && acc(y)
// @ ensures *x == old(*y) && *y == old(*x)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
```

## Exclusivity and aliasing
Clients may want to call `swap` with the same argument, e.g. `swap(x, x)`.
So far, our specification forbids this and we get the error:
``` go does_not_verify
// @ requires acc(x) && acc(y)
// @ ensures acc(x) && acc(y)
// @ ensures *x == old(*y) && *y == old(*x)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}

func client2() {
	x := new(int)
	y := new(int)
	*x = 1
	*y = 2
	swap(x, x)
	// @ assert *x == 1
}
```
``` go
Precondition of call swap(x, x) might not hold. 
Permission to y might not suffice.
```
Having `acc(x) && acc(y)` implies `x != y` since we are not allowed to have write access to the same location.
As a result, the precondition prevents us from calling `swap(x, x)`.

One possibility is to perform a case distinction in the specification on `x == y`.
While this works, the resulting specs are verbose, and we better refactor them to a reduced form.
``` go
// @ requires x == y ==> acc(x)
// @ requires x != y ==> acc(x) && acc(y)
// @ ensures x == y ==> acc(x)
// @ ensures x != y ==> acc(x) && acc(y)
// @ ensures x != y ==> *x == old(*y) && *y == old(*x)
// @ ensures x == y ==> *x == old(*x)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}
```
1. `acc(x)` is needed in any case, hence it can be factored out
    ``` go
    // @ requires x == y ==> acc(x)
    // @ requires x != y ==> acc(x) && acc(y)
    // @ ensures x == y ==> acc(x)
    // @ ensures x != y ==> acc(x) && acc(y)
    ```
    becomes
    ``` go
    // @ requires acc(x)
    // @ requires x != y ==> acc(y)
    // @ ensures acc(x)
    // @ ensures x != y ==> acc(y)
    ```
2. Simplify the postconditions
    ``` go
    // @ ensures x != y ==> *x == old(*y) && *y == old(*x)
    // @ ensures x == y ==> *x == old(*x)
    ```
    with:
    ``` go
    // @ ensures *x == old(*y) && *y == old(*x)
    ```
    where the assertion is unchanged for the case `x != y` and we see it is equivalent for the case `x == y` by substituting `y` with `x`.

In the following subsection we additionally reduce the specification.
At the end of this section you can find the final contract which allows calling swap even in cases where `x` and `y` are aliases.

## Preserving memory access (`preserves`)
It is a common pattern that a function requires and ensures the same permissions.
In our example, `acc(x)` and `x != y ==> acc(y)` is both required and ensured:
``` go
// @ requires acc(x)
// @ requires x != y ==> acc(y)
// @ ensures acc(x)
// @ ensures x != y ==> acc(y)
```
We can simplify this using the keyword `preserves`, which is syntactical sugar for requiring and ensuring the same assertion.
``` go
// @ preserves acc(x)
// @ preserves x != y ==> acc(y)
```


## Final version of `swap`
``` go verifies
// @ preserves acc(x)
// @ preserves x != y ==> acc(y)
// @ ensures *x == old(*y) && *y == old(*x)
func swap(x *int, y *int) {
	tmp := *x
	*x = *y
	*y = tmp
}

func client2() {
	x := new(int)
	y := new(int)
	*x = 1
	*y = 2
	swap(x, x)
	// @ assert *x == 1
	swap(x, y)
	// @ assert *x == 2
	// @ assert *y == 1
}
```

