# Addressability, `@` and sharing

Variables are called _shared_ if their address is taken[^1].
Gobra requires us to mark variables as shared explicitly.
This should ensure that the programmer is aware, in which cases, Gobra employs reasoning about permissions.
We distinguish _shared arrays_ and _shared structs_ from their _exclusive_ counterparts.
Since if the address of an array or struct is never taken, we do not have to worry about data races, and reasoning about them is much easier.


## Shared variables with `@`

Variables are marked as _shared_ by appending the ampersand symbol to a variable name.
For a variable `a` we either write `a /*@@@*/` using an inline comment or equivalently `a@` in `.gobra` files:
``` go
func main() {
	a /*@@@*/ := 1
	// a@ := 1
    x := &a
}
```

Otherwise, if we try to take the address of a non-shared variable, Gobra reports an error:
``` go
func main() {
	a := 1
    x := &a
}
```
``` text
property error: got a that is not effective addressable
        x := &a
      ^
```

For structured variables of slice, shared array, or shared struct types, their elements or fields can be addressed individually.
Access can be specified for example to the first element of a shared array with `acc(&a[0])` or to the field `x` of a shared struct `c` with `acc(&c.x)`.

In the following example, we use structs representing 2D coordinates and implement a method `Scale` to multiply them by a scalar factor.
Gobra reports an error if we try to call `Scale` on a non-shared struct.
`Scale` is defined for a pointer receiver, and here the address of the struct is taken implicitly.

``` go
type Coord struct {
	x, y int
}

//@ requires acc(&c.x) && acc(&c.y)
//@ ensures acc(&c.x) && acc(&c.y)
//@ ensures res.x == old(c.x) * factor
//@ ensures res.y == old(c.y) * factor
func (c *Coord) Scale(factor int) Coord {
	return Coord{x: c.x * factor, y: c.y * factor}
}
func client1() {
	c := Coord{1, 2}
	// c /*@@@*/ := Coord{1, 2} // fix: mark c shared
	v := c.Scale(5)
	//@ assert v == Coord{5, 10}
}
```
``` text
ERROR Scale requires a shared receiver ('share' or '@' annotations might be missing).
```

As an exception, taking the address of a composite literal is allowed:
``` go
func client2() {
	c := &Coord{1, 2}
	v := c.Scale(5)
}
```

## `share`

> Parameters of a function or method can be shared with the `share` statement at the beginning of the body.

It is not possible to mark parameters with `@`, as the information on whether a parameter is shared is local to the function and should not be exposed in its signature.

``` go
func client3(c1, c2 Coord) {
	//@ share c1, c2
	v1 := c1.Scale(5)
	v2 := c2.Scale(-1)
}
```


[^1]: In Go, there is the notion of [addressability](https://go.dev/ref/spec#Address_operators) which clearly defines which operands are addressable.
