# Basic Specifications
<!--
Goals
- Specification by precondition and postcondition
- View them as contracts between the caller and callee
- //what the verifier checks//
- syntax to write basic contracts in Gobra
- Strength of Conditions
-->

In this section we introduce the verification of functions with preconditions and postconditions and how we can specify them in Gobra with `requires` and `ensures`.
First, we give an abstract overview and then take look at examples with Newton's Method.


In simple terms, we want to be sure that our functions compute what they should do.
But how can we differentiate between a correct and faulty implementation?
One person's feature may be another person's bug.
We need to formalize the idea of *computing what they should do*.
For this purpose, we introduce specifications.
Looking at functions, they come in the form of **preconditions** and **postconditions**.


It is the programmers job to write the specification, and it is Gobra's job to prove whether a function satisfies its specification.

1. A function's precondition must be satisfied whenever the function is called.
2. Assuming the precondition, the verifier must be able to deduce that the postcondition of a function holds whenever it returns.

If the first two points hold, the caller can assume that the precondition holds.

<!-- TODO  link modes of failure
Precondition of call foo(-5) might not hold.
Postcondition might not hold.
-->

We can view it as a contract between the caller and the callee:
The caller must satisfy the precondition.
Likewise, the callee must satisfy the postcondition.



## Motivational Example

We will use [Newton's Method]( https://en.wikipedia.org/wiki/Newton's_method) as an example.
It can be used to approximate zeroes of continuous functions.
One use case is to compute the square root of \( y > 0\).
<!-- The function \( f(x) = y - x^2\) has a zero for \( x = \sqrt{y} \) -->
<!-- \[ x_{k+1} := \frac{x_k}{2} + \frac{y}{2 x_{k}}\] -->
The iteration is given by:
\\[ x_{k+1} := \frac{1}{2} \left( x_k + \frac{y}{x_{k}} \right) \\]
<!-- Careful: for int this is always zero -->
<!-- 1/2 * (x + y / x) -->
With a straightforward implementation in Go.
```go
func newton(x, y int) int {
	return x/2 + y / 2 / x
}
```
Note that for now, we use `int` instead of floating-point numbers.
```go
// we can use x=y as an initial guess
newton(4, 4) // 2
// For y=9 we need two iterations
newton(9, 9) // 4
newton(4, 9) // 3
// Since we use ints we are imprecise
newton(2, 2) // 1
```
The programmer may have written a comment.
```go
// Approximate the sqrt of y which is positive
// res is the next iterate of Newton's method using x
// as the previous iterate or initial guess
// x must not be 0
func newton(x, y int) (res int) {
	return x/2 + y / 2 / x
}
```

<!-- panic: runtime error: integer divide by zero -->
Parsing the comment we extract the following assumptions
- For `x==0` we run into a divide by zero error and the program `panics`
- The square root is only defined for positive numbers so we require `y>0` 

Of course, we could add checks for these conditions and add error handling.
```go
~import (
	~"errors"
	~"fmt"
~)
~func newton(x, y int) int {
	if y <= 0 {
		panic(fmt.Errorf("Requires y > 0 but got y = %d instead", y))
	}
	if x == 0 {
		panic(errors.New("Requires x != 0 but got x = 0"))
	}
	~return x/2 + y / 2 / x
~}
```
These checks happen dynamically (at runtime).
Next, we show how Gobra can verify that we never run into a situation where the checks would trigger.

## Precondition and Postconditions in Gobra
Go conveniently has named returned values that allow us to document them and also use them in specifications.
In Gobra we can add preconditions with the keyword `requires`

```go
//@ requires x != 0 && y > 0
func newton(x, y int) int
```
Instead of combining both assertions with the logical and operator, we can equivalently write them on two lines:
```go
//@ requires x != 0
//@ requires y > 0
func newton(x, y int) int
```
If we now try to call `newton` with disallowed values, Gobra reports an error.
```go
~func client() {
newton(4, 4)  // verifies
newton(4, -1) // error: Assertion y > 0 might not hold.
newton(0, 4)  // error: Assertion x != 0 might not hold.
~}
```
<!-- TODO talk about only first error reported -->
For constant values this is easy to check.
But what if we have an `arg` we know nothing about?

```go
func client(arg int) {
	newton(4, arg) // error: Assertion y > 0 might not hold.
	newton(arg, 4) // error: Assertion x != 0 might not hold.
}
```
Similarly, we can add a postcondition with the keyword `ensures`
``` go
//@ ensures res >= 0
func square(x int) (res int) {
	return x * x
}
```
Gobra has to check, that for an arbitrary integer `x`, the result is always non-negative.
In this case, it succeeds, but in general, this can be a hard problem and the verifier may  [time out](./basic-specs.md#verifier-timeout)

In the comments, we write informally what we know about the variables at that point.
```go
func client(arg int) {
	// {arg: ?}
	squared := square(arg)
	// {arg: ?, squared >= 0}
	r := newton(4, squared) // verifies
	// {arg: ?, squared >= 0, r: ?}
}
```


`newton(squared, 4)`
If we naïvely tried to change the postcondition to `ensures res > 0` ...
<!-- TODO error -->

<!-- we don't know that squared == arg * arg -->
<!-- assert -->

<!-- example with both pre and postcondition -->
```go
//@ requires x > 0
//@ requires n >= 2
//@ ensures res > 0
func newton_iteration(x int, n int) (res int) {
	return x/2 + n / x / 2
}
```
<!-- Exercise: find a counterexample
x==1 and n==1 ) -->

<!-- Unrolling a loop -->
``` go
//@ requires n > 100
func foo(n int)
	initial_guess := n
	x := newton_iteration(initial_guess, n)
	x  = newton_iteration(x, n)
	x  = newton_iteration(x, n)
	// even
	for {
		x  = newton_iteration(x, n)
	}
	// we will write about termination later
}
```

<!-- strength of conditions -->
<!--  strengthen pre, weaken post -->
<!--  Overconstraining e.g. if they imply false -->
<!-- talk about default assertions -->

<!-- what is syntactically allowed in an assertion -->

 
## Verifier Timeout
```go
//@ requires x > 0.0
//@ ensures res > 0.0
func newton_iteration(x float32, n float32) (res float32) {
	return x/2 + n / x / 2
}
```
<!-- TODO why? -->

<!-- ### Order of errors -->
<!-- Gobra reports only the first error it encounters. -->
<!-- ``` go -->
<!-- //@ requires false -->
<!-- func foo() {} -->

<!-- func main() { -->
<!-- 	foo()  // Error: Assertion false might not hold. -->
<!-- 	assert false -->
<!-- } -->
<!-- ``` -->

## Section Quiz
### Does it verify?
<!-- TODO make one with a "occluded" false -->
```gobra
requires false
ensures true
func foo() {}
```

### Strength
TODO: make it harder
Quiz: which condition is stronger
`requires x != 0`
`requires x  > 0`
`requires x >= 0`

## Full Code Example
TODO
