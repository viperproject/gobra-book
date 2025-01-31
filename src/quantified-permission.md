# Quantified permissions

We speak of _quantified permission_ when access predicates occur within the body of a `forall` quantifier[^1].

This may simplify specifying access to shared arrays, but importantly, it
allows us to specify access to a _possibly unbounded number of locations_ [^2].
Whereas arrays have a fixed number of elements, the type of a slice does not contain its length.
In the next section on [slices](./slices.md), we will use quantified permission to handle their dynamic size.
For example, the following precondition specifies write access to all elements of a slice `s`:
``` go
// @ requires forall i int :: {s[i]} 0 <= i && i < len(s) ==> acc(&s[i])
func addToSlice(s []int, n int)
```

## Shared arrays
For shared arrays, using quantified permissions is not compulsory.
As an array has a fixed number of elements, we could simply list access to each element.
In the following example, we look at how we can concisely specify access to the elements of a shared array.

functions reversing the elements in arrays and 

We mark the array `a` as [shared with `/*@@@*/`](./addressable.md).
Now, we may reference it and pass its address to the function `reverseInplace`.
This function reverses the elements by swapping the first element with the last one, the second element with the second last element, and so on, until the entire array is reversed.
Note that the loop invariant must also capture which part of the array is still unmodified.
This allows the array to be reversed in place, as long as permissions are held to modify its elements.
Each element of an array is addressable, and with quantified permissions we can specify access to each with the following assertion, as seen in the contract of `reverseInplace`:
``` gobra
forall i int :: 0 <= i && i < N ==> acc(&((*p)[i]))
```
Note that we must dereference the pointer first and that we have access to the location `&((*p)[i])`, not the value `(*p)[i]`.
``` go
{{#include shared_array.go:reverseInplace}}

{{#include shared_array.go:client1}}
```

We can be more specific and have access to single elements.
For example, to increment the first element, only `acc(&a[0])` is required.
``` go
{{#include shared_array.go:client2}}
```

For a pointer to an array, we can use the syntactic sugar `acc(p)` which is short for access to each element
(`forall i int :: 0 <= i && i < N ==> acc(&((*p)[i]))`).


Note that we can still call the function `reverse` with a shared array.
The fact that a variable is shared is local; in this case, only within the scope of `client3`.
`reverse` returns a new, reversed array.
It requires no permissions as the array is copied.
But in `client3`, at least read permission must be held to call `reverse(a)`.
If we [exhale](./inhale-exhale.md) access to the shared array, we can no longer pass `a` as an argument.
``` go
{{#include shared_array.go:reverse}}
{{#include shared_array.go:client3}}
```
``` text
ERROR Reading might fail. 

Permission to a might not suffice.
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
