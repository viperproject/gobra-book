# Pure functions

A function that is deterministic and has no side effects can be marked as `pure` and may be used in specifications and proof annotations.

<!-- We are not allowed to call arbitrary functions in specifications. -->
If we try to call a normal Go function `Cube` in an assert statement, Gobra reports errors:
``` go
package main

func Cube(x int) int {
    return x * x * x
}

func client() {
    // @ assert 8 == Cube(2)
}
```
``` text
ERROR /tmp/playground.go:8:9:error: expected pure expression, but got '8 ==  Cube(3)'
    assert 8 == Cube(3)
        ^
ERROR /tmp/playground.go:8:14:error: ghost error: Found call to non-ghost impure function in ghost code
    assert 8 == Cube(3)
             ^
```
Let us mark the function `Cube` as `pure`, and also with `decreases`, since a termination measure is a requirement for a pure function.
Gobra enforces the syntactic requirement that the body of `pure` functions must be a single return with a pure expression, which is satisfied in this case.
``` go
// @ pure
// @ decreases
func Cube(x int) int {
    return x * x * x
}

// @ requires n >= 0
func client(n int) {
    // @ assert 8 == Cube(2)
    // @ assert Cube(2) >= 8 && Cube(2) <= 8
    r := Cube(2)
// @ assert Cube(n) >= 0
}
```
Note that we may call pure functions in normal (non-ghost) code, unlike ghost functions.
The assertion passes, even without a postcondition.
Unlike normal functions, Gobra may peek inside the body of a function.
For example, `Cube(n)` can be treated as `n * n * n`
<!--
## Side effects and nondeterminism
Pure functions correspond to mathematical functions, which we use when reasoning about them.
For example, `assert Cube(2) == 8` and `assert Cube(2) >= 8 && Cube(2) <= 8` are equivalent.
Now if `Cube` were nondeterministic, the calls `Cube(2)` and `Cube(2)` with the same output might produce different outputs.
Hypothetically, if we could call non-deterministic functions in proof annotations, the verification verdict would become nondeterministic in turn.
This is clearly undesirable; the same program shall either verify or not.
To be precise, specifications are not executed like normal Go code, so we could not simply run a nondeterministic function and use its output.
The arguments might not be concrete, as in the above example, where we assert `Cube(n) >= 0` for an arbitrary positive integer `n`.

If `Cube` had side-effects, `assert Cube(2) == 8` and `assert Cube(2) >= 8 && Cube(2) <= 8` could again not be treated as equivalent.
The interpretation of side effects, such as modifying memory, allocating memory, or input/output, is not clear for specifications and proof annotations.
Consider the hypothetical example where a pure function `sideEffect` could increment a global variable.
Now if another function `foo` had the precondition `a == sideEffect()`, would we need to account for the side effect once, or for every call of `foo`?
This is not allowed in any case, since specifications are ghost code, so non-ghost state must not be modified.
Still, if only ghost state is affected, keeping track of the side effects would break modular reasoning.
-->

## Specifying functional correctness with pure functions
We define a `pure` function `fibonacci` as a mathematical reference implementation, following the recursive definition of the [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_sequence).
While recursion is not idiomatic in Go, recursion is often used for specifications.
In the end, our goal is to verify the functional correctness of an iterative implementation that can be defined in terms of the pure function.
``` go
// @ requires n >= 0
// @ ensures res == fibonacci(n)
func fibIterative(n int) (res int) {
	a, b := 0, 1
	for i := 0; i < n; i++ {
		a, b = b, a + b
	}
	return a
}
```

## Syntactic restriction
Gobra enforces the syntactic restriction that the body of `pure` functions must be a single return with a pure expression.
Hence, we are unable to define `fibonacci` with an `if` statement:
``` go
// @ requires n >= 0
// @ pure
// @ decreases n
func fibonacci(n int) (res int) {
    if n <= 1 {
        return n
    } else {
        return fibonacci(n-1) + fibonacci(n-2)
    }
}
```
``` text
ERROR /tmp/playground.go:17:33:error: For now, the body of a pure block is expected to be a single return with a pure expression, got Vector(if n <= 1 {
  return n
} else {
  return  fibonacci(n - 1) +  fibonacci(n - 2)
}
) instead
func fibonacci(n int) (res int) {
                                ^
```

Instead, we can resort to the conditional expression `cond ? e1 : e2`, which evaluates to `e1` if `cond` holds, and to `e2` otherwise:
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
An error is reported since the conditional expression is a ghost operation.
The error can be avoided by declaring the out parameter as `(ghost res int)`, but we prefer to mark the entire function `ghost`, as this function is not valid Go code.
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

## Pure functions are transparent
Unlike normal functions, where we cannot peek inside their body, 
Gobra learns the body of `pure` functions when calling them.
The following assertions pass, without having specified a postcondition.
``` go
func client1(n int) {
    if n > 1 {
        // @ assert fibonacci(n) == fibonacci(n-1) + fibonacci(n-2)
    } else if n == 0 {
        // @ assert fibonacci(n) == 0
    }
}
```
<!-- We may still specify postconditions -->

Note that this does not automatically happen for the recursive calls in the body.
For example, we can assert `fibonacci(3) == fibonacci(2) + fibonacci(1)`, but not `fibonacci(3) == 2`.
``` go
func client2() {
    // @ assert fibonacci(3) == fibonacci(2) + fibonacci(1)
    // @ assert fibonacci(3) == 2
}
```
``` text
ERROR Assert might fail. 
Assertion fibonacci(3) == 2 might not hold.
```
By providing additional proof goals, we can to assert `fibonacci(3) == 2`.
Having previously asserted `fibonacci(1) == 1` and `fibonacci(2) == 1`, these can be substituted in `fibonacci(3) == fibonacci(2) + fibonacci(1)`.
``` go
func client3() {
    // @ assert fibonacci(0) == 0
    // @ assert fibonacci(1) == 1
    // @ assert fibonacci(2) == 1
    // @ assert fibonacci(3) == 2
}
```

<!-- ``` go -->
<!-- // @ assert forall n int :: {fibonacci(n)} n >= 2 ==>  fibonacci(n) == fibonacci(n-1) + fibonacci(n-2) -->
<!-- // @ assert fibonacci(10) == 55 -->
<!-- // Not exponential! -->
<!-- // @ assert fibonacci(88) == 1100087778366101931 -->
<!-- // fibIterative(93) -> -6246583658587674878   // OVERFLOW -->
<!-- // @ assert fibonacci(100) == 3736710778780434371 -->
<!-- ``` -->

## Exercise: iterative Fibonacci
We leave it as an exercise to provide invariants for an iterative implementation satisfying the specification.

{{#quiz ../quizzes/basic-ghost-pure.toml}}

## Ghost and pure functions
Often, we will mark a function both `ghost` and `pure`.
Although the concept of pure and ghost functions is orthogonal:
a function may be ghost, pure, ghost and pure, or neither.
Note that a ghost function may have side effects, e.g. modifying a ghost variable.

## Termination of `pure` functions
By now we know that `pure` functions can be used in specifications,
and since they do not have side effects nor non-determinism, they can be thought of as mathematical functions.
To prevent inconsistencies, termination measures must be provided for `pure` functions:

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
pure
decreases _ // assuming termination
ensures res != 0
func incons(x int) (res int) {
    return 2 * incons(x)
}

func foo() {
    assert incons(1) == 2 * incons(1) // (1)
    assert incons(1) / incons(1) == 2 // (2)
    assert 1 == 2                     // (3)
    assert false
}
```
The assertions all pass since
1. We saw that we can replace the call of a `pure` function with its body.
2. Divide both sides by `incons(1)` (without the precondition `ensures res != 0`, Gobra reports the error `Divisor incons(1) might be zero`.)
3. Arithmetic
4. We found the contradiction `1 == 2`, or equivalently `false`.

