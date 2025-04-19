# Ghost code

Often, it is useful to introduce _ghost state_ and _ghost code_, i.e., additional state and code that is used for specification and verification purposes, but which is not compiled and executed.
Ghost code cannot change the visible behavior of a program, i.e., it cannot assign to non-ghost variables or cause the program to not terminate.
Ghost code is considered by Gobra, but it is ignored during compilation.
When writing Gobra annotations in Go source files, the syntax `// @` makes it clear that the line is treated as a comment by Go and is not included in the program.

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
The updated contract specifies that the maximal value is at index `idx`.
We update `idx` with a ghost statement to maintain the invariant that it is the index of the maximal value in the prefix of the array already traversed.
As `Max` has two out parameters now, clients  must assign the ghost return value to a ghost location.
``` go verifies
{{#include max.go}}
```
<!-- todo if not declared before, it is inferred automatically for the := assignment -->

## Ghost erasure property
Recall that ghost code cannot change the visible behavior of a program.
Hence, ghost code cannot modify non-ghost locations.
For example, the ghost statement `x = 1` causes an error since `x` is a normal variable:
``` go does_not_verify
var x int
// @ ghost x = 1
// ...
```
``` text
ERROR ghost error: only ghost locations can be assigned to in ghost code
```

To make a statement ghost, add `ghost` before it.
However, not all statements can appear in ghost code.
For example, there is no ghost `return` statement because it can change the visible behavior of a program:
``` go does_not_verify
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
``` go does_not_verify
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

We will continue using `ghost` code in the following chapters.

