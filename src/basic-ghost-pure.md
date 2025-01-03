# Ghost Code and `pure` Functions

> Often, introducing additional state, such as additional variables or arguments is useful for specification and verification.

We call code `ghost` that exists solely for the purpose of verification.
It vanishes when the program is compiled.
Hence **non**-`ghost` code is not allowed to refer to any `ghost` code.
When writing Gobra annotations in Go source files, the syntax `//@ ` makes it clear that the line is treated as a comment by Go and not included in the program.


A function that is deterministic and has no side effects can be marked as `pure` and may be used in specifications.
This allows us to abstract specifications.


## A `pure` and `ghost` Function
In the [binary search section](./loops-binarysearch.md), we relied on the precondition that an array `arr` is sorted:
``` gobra
requires forall i, j int :: 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
```
If we want to write clients that use `binarySearch` we have to propagate the preconditions, for example, we might want to write `insert`:
``` go
// @ requires forall i, j int :: 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
func insert(arr [N]int, value int) {
	var fresh [N + 1]int
	idx := binarySearch(arr, value)
    // ...
}
```

In the spirit of *don't repeat yourself* we want to abstract the precondition.
Our first attempt is:
``` go
func isArraySorted(arr [N]int) bool {
	//@ invariant 1<=i && i <= len(arr)
	for i:=1; i<len(arr); i++ {
		if arr[i-1] > arr[i] {
			return false
		}
	}
	return true
}

//@ requires isArraySorted(arr)
func insert(arr [N]int, value int) {
    // ...
}
```
But we get the error:
``` text
error: ghost error: Found call to non-ghost impure function in ghost code
requires isArraySorted(arr)
         ^
```

Recall:
> Assertions are boolean expressions that are deterministic and have no side effects.

We are not allowed to call arbitrary functions in specifications!
Here are two simple functions with a side effect or with nondeterminism:
``` go
import "time"
var x = 0
func sideEffect(p *int) int {
    *p += 1
    return 0
}
func nonDeterministic() int {
    return int(time.Now().UnixNano() % 100)
}
```

Actually `isArraySorted` has no side effects.
But Gobra does not automatically infer this.
This is where `pure` comes into play.

We can mark a function with the `pure` keyword.
Note that it must come before `func` and after the pre and postconditions.
``` go
//@ pure
func isArraySorted(arr [N]int) bool {
	~//@ invariant 1<=i && i <= len(arr)
	~for i:=1; i<len(arr); i++ {
		~if arr[i-1] > arr[i] {
			~return false
		~}
	~}
	~return true
}
```
``` text
error: For now, the body of a pure block is expected to be a single return with a pure expression, got Vector(  omitted...
```

Due to the syntactical restrictions, we need another way to express it.
As an attempt, we could try to return the assertion from the precondition:
``` go
func isSorted(arr [N]int) bool {
	return forall i, j int :: 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
}
```
But `forall` is not valid in Go code.
We can make the function `ghost` by inserting the `ghost` keyword before the other specifications:
``` go
/*@ 
ghost
pure
decreases
func isSorted(arr [N]int) bool {
	return forall i, j int :: 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
}
@*/

//@ requires isSorted(arr)
func insert(arr [N]int, value int) {
    // ...
}
```
The above version verifies.
Note that we had to add `decreases`; we explain shortly why this is necessary.


## Fibonacci
While recursion is not idiomatic in Go it is often used for specifications.
As an example, we look at the famous `fibonacci` function.
Due to the syntactical limitations of `pure` functions, we are not allowed to use `if` statements in their bodies.
Instead, we resort to the conditional expression `cond ? e1 : e2`:
``` go
// @ requires n >= 0
// @ pure
// @ decreases n
func fibonacci(n int) (res int) {
    return n <= 1 ? n : fibonacci(n-1) + fibonacci(n-2)
}
```
``` text
Error at: </home/gobra/fibonacci.go:6:24> ghost error: ghost cannot be assigned to non-ghost
func fibonacci(n int) (res int) {
                       ^
```
We got an error because Go does not support the ternary operator and `fibonacci`'s body contains `ghost` code.
The error can be avoided by declaring the out parameter as `(ghost res int)` but it is preferred to make the entire function `ghost`:
``` go
/*@
ghost
requires n >= 0
decreases n
pure
func fibonacci(n int) (res int) {
    return n <= 1 ? n : fibonacci(n-1) + fibonacci(n-2)
}
@*/
```
Note that we do not have to specify postconditions.
As opposed to normal functions where we cannot peek inside them, 
calls to `pure` functions can be thought of as inlined.
The following assertions pass:
``` go
func client(n int) {
    if n > 1 {
        //@ assert fibonacci(n) == fibonacci(n-1) + fibonacci(n-2)
    } else if n == 0 {
        //@ assert fibonacci(n) == 0
    }
}
```

We leave it as an exercise in the Quiz to provide invariants for an iterative implementation satisfying the specification:
``` go
// @ requires n >= 0
// @ ensures res == fibonacci(n)
func fibIterative(n int) (res int)
```

## Ghost Erasure
Ghost code must not affect actual code.
The behavior of a program with ghost code, and with ghost code erased must be the same.
For example, if we try to modify a variable `x` with a ghost statement.
To make a statement ghost, add `ghost` before it.
``` go
	var x int
	//@ ghost x = 1
	// ...
```
``` text
ghost error: only ghost locations can be assigned to in ghost code
```
Gobra detects that modifying `x` could clearly alter the output of the program.

The control flow must also not diverge.
We are not allowed to make any statement `ghost`, for example if we try to exit early out of the function `loop`, this would change its (termination) behavior.
``` go
func loop() {
	//@ ghost return
	for {}
}
```
But this is not permitted:
``` text
ghost error: expected ghostifiable statement
```

## Termination of `ghost` functions
Termination measures must be provided for `ghost` functions.
This is also to ensure that their presence does not change the program's behavior.
As a simple example, assume that `inf()` does not terminate.
``` go
func boo()  {
	//@ ghost y := inf()
	return 0
}
```
Clearly, `boo` loops with ghost code and returns immediately without.


## Termination of `pure` functions
By now we know that `pure` functions can be used in specification,
and since they do not have side effects or non-determinism they can be thought of as mathematical functions.
To prevent inconsistencies, termination measures must be provided for `pure` functions, otherwise, we see errors like:

``` gobra
pure
ensures res != 0
func incons(x int) (res int) {
	return 2 * incons(x)
}
```
``` text
All pure or ghost functions and methods must have termination measures, but none was found for this member.
pure
```
Next, we show why it is a bad idea to have non-terminating specification functions and derive `assert false`.
For this we assume that `incons` terminates by giving it the wildcard termination measure `decreases _`.

``` gobra
~pure
~decreases _ // assume termination
~ensures res != 0
~func incons(x int) (res int) {
	~return 2 * incons(x)
~}

func foo() {
	assert incons(1) == 2 * incons(1) // (1)
	assert incons(1) / incons(1) == 2 // (2)
	assert 1 == 2                     // (3)
	assert false
}
```
The assertions all pass since
1. We saw that we can replace the call of a `pure` function with its body.
2. Divide both sides by `incons(1)` (what would happen without the precondition `ensures res != 0`? [^1])
3. Arithmetic
4. We found the contradiction `1 == 2`, or equivalently `false`.

## Ghost Parameter
Let us look at the function `max` that returns the maximum element of a non-empty array with signature:
``` go
//@ requires len(arr) > 0
//@ ensures forall i int :: 0 <= i && i < len(arr) ==> arr[i] <= res
//@ ensures exists i int :: 0 <= i && i < len(arr) ==> arr[i] == res
func max(arr [N]int) (res int)
```
Verifying this function would be challenging because of the `exists` quantifier.
Additionally, the postcondition gives clients only the maximal value.

With a `ghost` out parameter `idx` we can return the index of the maximal value.

``` go
//@ requires len(arr) > 0
//@ ensures forall i int :: 0 <= i && i < len(arr) ==> arr[i] <= res
//@ ensures 0 <= idx && idx < len(arr) && arr[idx] == res
func max(arr [N]int) (res int /*@ , ghost idx int @*/) {
	res = arr[0]
    //@ idx = 0
	//@ invariant 0 <= i0 && i0 <= N
	//@ invariant forall j int :: 0 <= j && j < i0 ==> arr[j] <= res
	//@ invariant 0 <= idx && idx < N && arr[idx] == res
	for i, a := range arr /*@ with i0 @*/ {
		if a > res {
			res = a
			//@ idx = i
		}
	}
	return res /*@ , idx @*/
}
```
Now when calling `max` we must also assign to a `ghost` variable:
``` go
~arr := [N]int{-2, 2, 1, 5, 5}
//@ ghost var idx int
m, /*@ idx @*/ := max(arr)
```

## More Ghosts
<!-- from tutorial.md -->
In general, in Gobra there are:
- ghost in and out parameters `ghost idx, int`
- ghost functions where all in- and out-parameters are implicitly ghost
- ghost methods
- ghost variables `ghost var x int = 42` 
- ghost statements (if-then-else, loops)
- ghost types (e.g. sequences, sets, multisets)

We will continue to use `ghost` code in the following chapters.


## Quiz
{{#quiz ../quizzes/basic-ghost-pure.toml}}

## Footnotes
[^1]: Without `ensures res != 0`, Gobra reports an error for `assert incons(1) / incons(1) == 2`:
``` gobra
Assert might fail. 
Divisor incons(1) might be zero.
```
