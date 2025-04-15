# Addressability, `@` and sharing

If we try to take the address of a local variable, Gobra reports an error:
``` go does_not_verify
func main() {
	b := 1
	x := &b
}
```
``` text
property error: got b that is not effective addressable
	x := &b
		^
```
To reference local variables, they must be marked as _shared_ by appending the ampersand symbol to a variable name.
Then, Gobra uses permissions to track access to this location.
For a variable `b`, we either write `b /*@@@*/` using an inline annotation or `b@` equivalently in `.gobra` files.

``` go verifies
func main() {
	b /*@@@*/ := 1
	// b@ := 1 // .gobra version
	x := &b
	inc(x)
	// @ assert b == 2
}

// @ preserves acc(p)
// @ ensures *p == old(*p) + 1
func inc(p *int) {
	*p = *p + 1
}
```
With a pointer, a variable can be modified outside the function where it is defined.
Note that otherwise, permissions are not required to reason about local variables.
When passed as arguments to functions, the values are copied, and the original variables are not modified.

Sharing applies to local variables of any type.
In this section, we specifically look at _shared structs_.
An example with _shared arrays_ is shown in a [following section](./quantified-permission.md).

## Shared structs
The fields of structs can be addressed individually.
For example, access can be specified to the field `x` of a shared struct `c` with `acc(&c.x)`.

In the following example, we use structs representing 2D coordinates and implement a method, `Scale,` to multiply them by a scalar factor.
``` go does_not_verify
{{#include shared_struct.go:Scale}}

func client1() {
	c := Coord{1, 2}
	c.Scale(5)
	// @ assert c == Coord{5, 10}
}
```
``` text
ERROR Scale requires a shared receiver ('share' or '@' annotations might be missing).
```
Gobra reports an error if we try to call `Scale` on a non-shared struct.
`Scale` is defined for a pointer receiver, and here, the address of the struct is taken implicitly.
The error message is instructive, and we can fix this by marking `c` as shared:
``` go verifies
{{#include shared_struct.go:client1}}
```

Composite literals are addressable.
We may reference them directly without errors:
``` go verifies
{{#include shared_struct.go:client2}}
```

## Shared parameters (`share`)
It is not possible to mark parameters with `@`, as whether a parameter is shared is local to the function and should not be exposed in its signature.
Gobra reports errors as we cannot reference the non-shared `c1` and `c2` to call `Scale` on a pointer receiver.
``` go does_not_verify
func client3(c1, c2 Coord) {
	c1.Scale(5) // error
	c2.Scale(-1) // error
}
```
``` text
ERROR Scale requires a shared receiver ('share' or '@' annotations might be missing).
	c1.Scale(5)
    ^
ERROR Scale requires a shared receiver ('share' or '@' annotations might be missing).
	c2.Scale(-1)
    ^
```
The parameters of a function or method can be shared with the `share` statement at the beginning of the body.
``` go verifies
{{#include shared_struct.go:client3}}
```
This resolves the errors above.


<!-- [^1]: In Go, there is the notion of [addressability](https://go.dev/ref/spec#Address_operators) which clearly defines which operands are addressable. -->
