# Quantified permissions

We speak of _quantified permission_ when access predicates occur within the body of a `forall` quantifier[^1].

This may simplify specifying access to shared arrays, but importantly, it
allows us to specify access to a _possibly unbounded number of locations_.
Whereas arrays have a fixed number of elements, the type of a slice does not contain its length.
In the next section on [slices](./slices.md), we will use quantified permission to handle their dynamic size.
For example, the following precondition specifies write access to all elements of a slice `s`:
``` go
// @ requires forall i int :: {s[i]} 0 <= i && i < len(s) ==> acc(&s[i])
func addToSlice(s []int, n int)
```

## Injectivity requirement

As a requirement, the mapping between instances of the quantified variable and the receiver expression must be injective.
In the example `addToSlice`, this injective mapping is from `i` to `&s[i]`.

In the following example, the postcondition of `getPointers` does not specify that the returned pointers are all distinct.
Gobra cannot prove that the mapping is injective and reports an error.
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

We can explicitly specify that the pointers are distinct:
``` go
// @ ensures acc(ps[0],1/2) && acc(ps[1],1/2) && acc(ps[2],1/2)
// @ ensures forall i, j int :: {ps[i], ps[j]} 0 <= i && i < j && j < len(ps) ==> ps[i] != ps[j]
```
Alternatively, we can use quantified permissions for the postcondition, which implies the injectivity:
``` go
// @ ensures forall i int :: {ps[i]} 0 <= i && i < len(ps) ==> acc(ps[i], 1/2)
```

<!-- Note that without this requirement, an array like `[3]*int{&a, &a, &a}` could be passed to `consumer` and permission `acc(&a, 1/2)` would be inhaled three times, a contradiction. -->


[^1]: Can access predicates occur within the body of the `exists` quantifier?
The short answer is no.
Consider the hypothetical precondition `requires exists i int :: acc(&s[i])`.
This is not helpful because it would provide access to _some_ element of the slice `s`, but we cannot determine which element, as Gobra does not provide an instance of `i`.

[^2]: Recursive data structures, such as a linked list, can also introduce an unbounded number of locations. In chapter 3 we explore how _recursive predicates_ can be used in this case.
