# Quantified permissions

Access predicates can occur within the body of a `forall` quantifier[^1] .
For example:
``` go
// @ requires forall i int :: {s[i]} 0 <= i && i < len(s) ==> acc(&s[i])
func addToSlice(s []int, n int)
```

This allows us to specify access to a **possibly unbounded number of locations**.
When we used arrays in chapter 1 we did not have to use permissions since arrays are values and are copied in Go.
But when we accessed arrays or structs via a pointer we needed permission.
Both arrays and structs have a fixed number of elements (or fields)
whereas a slice of type `[]T` does not contain information regarding its length.
*Quantified Permissions* allow us to handle dynamic sizes [^2].

## Injective resources

As a requirement, the mapping between instances of the quantifier and the receiver expression must be injective.
In the above example this (injective) mapping is from `i` to `&s[i]`.
Gobra reports an error if it cannot prove this.
In the following example, the postcondition of `getPointers` does not specify that the returned pointers are all distinct.
``` go
// @ ensures acc(ps[0],1/2) && acc(ps[1],1/2) && acc(ps[2],1/2)
func getPointers() (ps [3]*int) {
	a /*@@@*/, b /*@@@*/, c /*@@@*/ := 0, 1, 2
	return [...]*int{&a, &b, &c}
}
// @ requires forall i int :: {ps[i]} 0 <= i && i < len(ps) ==> acc(ps[i], 1/2)
func consumer(ps [3]*int) { /* ... */ }

func client() {
	ps := getPointers()
	consumer(ps)
}
```
``` text
ERROR Precondition of call consumer(ps) might not hold. 
Quantified resource ps[i] might not be injective.
```

We can explicitly specify that the addresses are distinct:
``` go
// @ ensures acc(ps[0],1/2) && acc(ps[1],1/2) && acc(ps[2],1/2)
// @ ensures forall i, j int :: {ps[i], ps[j]} 0 <= i && i < j && j < len(ps) ==> ps[i] != ps[j]
```
Or by using quantified permissions for the postcondition, which implies the injectivity:
``` go
// @ ensures forall i int :: {ps[i]} 0 <= i && i < len(ps) ==> acc(ps[i], 1/2)
```

Note that without this requirement, an array like `[3]*int{&a, &a, &a}` could be passed to `consumer` and permission `acc(&a, 1/2)` would be inhaled three times, a contradiction.


## Footnotes
[^1]: Can access predicates occur within the body of the `exists` quantifier?
The short answer is no.
Let us think about the hypothetical precondition `requires exists i int :: acc(&s[i])`.
This is not helpful as it would provide access to *some* element of the slice `s`,
but we do not know to which element as Gobra does not provide an instance of `i`.

[^2]: A linked list structure can also introduce an unbounded number of locations. To traverse it, given a head `Node`, we recursively need permission to follow the `next` pointers. *Recursive predicates*, which we study in Chapter 3, best handle this.
``` go
type Node struct {
    value int
    next *Node
}
```
