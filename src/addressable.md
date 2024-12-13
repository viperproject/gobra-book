# Addressability and Sharing

If we try to take the address of a variable, we get an error from Gobra:
``` go
~func main() {
	a := 1
    x := &a
~}
```
``` text
property error: got a that is not effective addressable
        x := &a
      ^
```
In Go there is the notation of [addressability](https://go.dev/ref/spec#Address_operators) that defines when we can take the address `&a`.
Gobra requires us to be explicit and mark the variable `a` as *shared*.
This is done by appending the ampersand symbol to a variable name (`a@`) or equivalently in a comment with `a /*@@@*/`. 
This should ensure that the programmer is aware, in which cases, Gobra employs the *permission machinery*.
For example, we only need permissions for a shared array.
While for an *exclusive* array, we do not have to worry about data races and reasoning about them is much easier.

For structured variables of slice, shared arrays, or shared struct types, their elements or fields can be addressed individually.
Access can be specified for example to the first element of a shared array with `acc(&a[0])` or to the field `x` of a shared struct `c` with `acc(&c.x)`.
Sometimes, an address is taken implicitly, as in the following example where the method `Scale` expects a receiver of type `*Coord`:
``` go
type Coord struct {
	x, y int
}

// @ requires acc(&c.x) && acc(&c.y)
func (c *Coord) Scale(factor int) Coord {
	return Coord{x: c.x * factor, y: c.y * factor}
}
func client1() {
	c := Coord{1, 2}
	// fix: mark c shared
	// c /*@@@*/ := Coord{1, 2}
	v := c.Scale(5)
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

## share
Parameters of a function or method can be shared with the `share` statement at the beginning of the body.
``` go
func client3(c1, c2 Coord) {
	//@ share c1, c2
	v1 := c1.Scale(5)
	v2 := c2.Scale(10)
}
```

