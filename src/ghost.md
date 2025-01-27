# Ghost code

Often, it is useful to introduce _ghost state_ and _ghost code_, i.e., additional state and code that is used for specification and verification purposes, but which is not meant to be compiled and executed.
Ghost code cannot change the visible behavior of a program, i.e., it cannot assign to non-ghost variables or cause the program to not terminate.
<!-- "it cannot cause the program to not terminate." also the reverse, cannot cause a  -->

Ghost code is considered by Gobra but it is ignored during compilation.
When writing Gobra annotations in Go source files, the syntax `// @` makes it clear that the line is treated as a comment by Go and is not included in the program.

<!-- ## TODO Ghost functions -->
<!-- limitation: no error if we call ghost function in go code -->
<!-- but error "Found call to non-ghost impure function in ghost code" -->

## Ghost parameters
Consider the function `Max` that returns the maximum element of an array, with the signature:
``` go
// @ ensures forall i int :: 0 <= i && i < len(arr) ==> arr[i] <= res
// @ ensures exists i int :: 0 <= i && i < len(arr) ==> arr[i] == res
func Max(arr [10]int) (res int)
```
Verifying this function would be challenging because of the existential quantifier.
Additionally, the postcondition gives clients only the maximal value.

With a `ghost` out parameter `idx`, we can return the index of the maximal value.
The updated contract specifies, that the maximal value is at index `idx`.
We update `idx` with a ghost statement to maintain the invariant that it is the index of the maximal value in the prefix of the array already iterated over.
As `Max` has two out parameters now, clients  must assign the ghost return value to a ghost location.
``` go
const N = 10

// @ ensures forall i int :: 0 <= i && i < len(arr) ==> arr[i] <= res
// @ ensures 0 <= idx && idx < len(arr) && arr[idx] == res
func Max(arr [N]int) (res int /*@ , ghost idx int @*/) {
	res = arr[0]
	// @ invariant 0 <= i0 && i0 <= N
	// @ invariant forall j int :: 0 <= j && j < i0 ==> arr[j] <= res
	// @ invariant 0 <= idx && idx < N && arr[idx] == res
	for i, a := range arr /*@ with i0 @*/ {
		if a > res {
			res = a
			// @ ghost idx = i
		}
	}
	return res /*@ , idx @*/
}

func client() {
    arr := [10]int{0, 2, 4, 8, 10, 1, 3, 5, 7, 9}
    // @ assert arr[4] == 10
    // @ ghost var idx int
    m, /*@ idx @*/ := Max(arr)
    // @ assert arr[idx] == m
    // @ assert m == 10
}
```


<!-- todo if not declared before, it is inferred automatically for the := assignment -->


## Ghost erasure property
Recall that ghost code cannot change the visible behavior of a program.
Hence, ghost code cannot modify non-ghost locations.
For example, the ghost statement `x = 1` causes an error since `x` is a normal variable:
``` go
	var x int
	// @ ghost x = 1
	// ...
```
``` text
ERROR ghost error: only ghost locations can be assigned to in ghost code
```
<!-- TODO Limitation: if the statement is not made ghost, there is no error but it updates the variable!
	var x int
	// @ x = 1
	// @ assert x == 1
	// @ assert x == 0  // ERROR
-->

To make a statement ghost, add `ghost` before it.
Although not all statements can appear in ghost code.
For example, there is no ghost `return` statement, because it can change the visible behavior of a program:
``` go
func loop() {
	// @ ghost return
	for {}
}
```
``` text
ERROR ghost error: expected ghostifiable statement
```


## Termination of `ghost` functions
Ghost functions must be proven to terminate.
Calling a non-terminating ghost function could change the visible behavior of a program.
For example, the function `boo` does not terminate with ghost code but returns immediately without ghost code..
``` go
/*@
ghost
func inf() {
	for {}
}
@*/

// @ decreases
func boo() int {
	// @ ghost inf()
	return 42
}
```
``` text
ERROR loop occurring in ghost context does not have a termination measure
	for {}
 ^
```

    

## More ghost entities
<!-- from tutorial.md -->
In general, Gobra allows marking the following entities as ghost:
- in and out parameters of functions and methods
- functions and methods where all in- and out-parameters are implicitly ghost
- variables `ghost var x int = 42` 
- statements <!--  (if-then-else, loops) -->
<!-- - ghost types (e.g. sequences, sets, multisets) -->

We will continue using `ghost` code in the following chapters.

