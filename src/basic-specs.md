# Basic Specifications
<!--
Goals
- Specification by precondition and postcondition
- View them as contracts between the caller and callee
  - where the errors occur
- what the verifier checks
- syntax to write basic contracts in Gobra
- Default pre and postconditions
-->
In this section, we introduce the verification of functions with preconditions and postconditions and show how we can specify them in Gobra with `requires` and `ensures`.
First, we give an abstract overview and then take a look at examples.

In simple terms, we want to be sure that our functions compute what they should do.
But how can we differentiate between a correct and faulty implementation?
One person's feature may be another person's bug.
We need to formalize the idea of *computing what they should do*.
For this purpose, we introduce specifications.
Looking at functions and methods, come in the form of **preconditions** and **postconditions**.

Similar to how the types of function parameters restrict what values can be passed to a function, preconditions allow us to specify an assertion that must hold whenever a function is called.
For example, we could require that a function is never called with an argument `x` equal to zero (`requires x != 0`).

Postconditions are assertions that must hold whenever a function returns.
An example postcondition could be that the return value `res int` of a function is always positive (`ensures r >= 0`).

Together they form a contract:
- A function can be called when the caller satisfies its preconditions.
- Assuming the precondition, we must be able to deduce that the postcondition of a function holds whenever it returns.
- Then the caller can assume the postcondition holds after the call.

It is the programmers job to write the specification, and it is Gobra's job to prove whether this contract is followed.

## Preconditions with `requires`
The function `newton` computes an approximation of the integer square root of `y`.
Using it as an example, we begin writing our first specifications and examine the error messages we may encounter.
```go
func newton(x, y int) int {
	return x/2 + y/2/x
}
``` 
Gobra can prove the absence of panics, and if we try to verify the following program, we get the error:
``` text
Assignment might fail. 
Divisor x might be zero.
```

To avoid the *divide by zero* error we should restrict `x` to be non-zero.
We can add this assertion as an annotation with the `requires` keyword before the function declaration.

```go
//@ requires x != 0
func newton(x, y int) int {
	return x/2 + y / 2 / x
}
```

Since the square root makes sense only for positive numbers we can additionally require `y > 0`.
We could combine the assertions with the conjunction `&&` as `requires x != 0 && y > 0` or equivalently write them on separate lines:
```go
//@ requires x != 0
//@ requires y > 0
func newton(x, y int) int
```

If we now try to call `newton` with forbidden values, Gobra reports errors at the callers site.
```go
func client() {
	newton(4, 4)
	newton(4, -1) // error
	newton(0, 4)  // error
}
```
``` text
Precondition of call newton(4, -1) might not hold. 
Assertion y > 0 might not hold.
```
The third call is also violating `newton`'s precondition (`Assertion y > 0 might not hold.`).
But Gobra stops the verification of the function `client` after finding the first error.
Gobra uses modular verification, so we could see both errors if the offending calls happen in different functions.

Gobra checks for each call that the precondition is satisfied.
For constant values, this is easy to check.
But what if we have an `arg` we know nothing about?
```go
func client(arg int) {
	newton(4, arg) // error: Assertion y > 0 might not hold.
	newton(arg, 4) // error: Assertion x != 0 might not hold.
}
```
<!-- and error prone -->
Of course, we could add checks for the preconditions manually.
We want to emphasize that these checks happen at runtime.
Gobra verifies beforehand, that the checks do not trigger for any call.
```go
func newton(x, y int) int
	if y <= 0 {
		panic(fmt.Errorf("Requires y > 0 but got y = %d instead", y))
	}
	if x == 0 {
		panic(errors.New("Requires x != 0 but got x = 0"))
	}
	return x/2 + y / 2 / x
}
```
Also, note that Gobra reports the error for the callers as they are violating the contract.


## Postcondition with `ensures`
If no specifications are given, the pre and postcondition default to `true`.
Hence this does not restrict how a function can be called.
Also, the caller gets no guarantee for the return value.

Note that in the above example, we only specified a precondition so the postcondition of `newton` is implicitly `true`.
With Gobra's `assert` statement we can explicitly  assertions.
This is a useful debugging tool.
``` go
r := newton(arg, 4)
//@ assert r >= 0
```
Verification happens modularly and a caller cannot peek into the body of a function.
The only thing the caller can assume is the postcondition.
Since in this case, it is `true` and gives no constraints for `r`.
We get the error:
``` text
Assert might fail. 
Assertion r >= 0 might not hold.
```

Similarly, we can add postconditions with the keyword `ensures`.
Go conveniently has named return values so we can use them in specifications.
``` go
//@ requires x > 0
//@ requires n >= 2
//@ ensures res > 0
func newton(x int, n int) (res int) {
	return x/2 + n / x / 2
}
```
Here Gobra must checks that for any integers with `x > 0` and `n >= 2`,
after executing the function body `res >= 0` must hold.

If we specify a stronger postcondition like `ensures res >= 2`,
verification fails:

``` text
Postcondition might not hold. 
Assertion res >= 2 might not hold.
```

Then `newton` does not satisfy this specification since for `x=1` and `n=2` the result is `1`.


With postcondition `res > 0`, we can now iteratively call `newton`.
In the comments, we note what information we have at that point in time.
``` go
//@ requires n > 100
func foo(n int)
	// {n > 0}
	x0 := n
	// {n > 0, x0 == n}
	x := newton(x0, n)
	// {n > 0, x0 == n, x > 0}
	x  = newton(x, n)
	// {n > 0, x0 == n, x > 0}
	// ...
```

<!-- ``` go -->
<!-- //@ ensures res >= 0 -->
<!-- func abs(n int) (res int) { -->
<!-- 	// {n = ?} -->
<!-- 	if n < 0 { -->
<!-- 		// {n < 0} -->
<!-- 		res = -n -->
<!-- 		// {n < 0, res} -->
<!-- 		return -n -->
<!-- 	} else { -->
<!-- 		// {n >= 0} -->
<!-- 		res = n -->
<!-- 		return -->
<!-- 	} -->
<!-- } -->
<!-- ``` -->
## Assertions
Until now we did not define what assertions can be.
They are boolean expressions from Go like you would use for the condition of an `if` statement with certain limitations.
Namely, they must be deterministic and side-effect-free.
We can't call arbitrary functions but only `pure` ones which we introduce soon.
Additionally they can contain implications (`==>`), conditionals (`cond ? e1 : e2`) and quantifiers (e.g. `exists x int :: n > 42`
, e.g. `forall x int :: x >= 5 ==> x >= 0`).
We will look at these constructs in later chapters.

## Overconstraining
By mistake, we might add contradicting assertions.
```go
//@ requires y > 0
//@ requires y < 0
func newtonNever(x, y int) int {
	return x/2 + y / 2 / x
}
```
Since `y > 0 && y < 0` implies `false`.
Now under normal circumstances, this function cannot be called 
unless `false` is already established.

## Summary
- Preconditions can be specified `requires ASSERTION`
- Postconditions can be specified with `ensures ASSERTION`
- The default pre and postcondition is `true`
- The caller of a function must satisfy the function's precondition
- Assuming the precondition, the postcondition must hold when a function returns
- After a call, the caller can assume the postcondition
- Assertions are boolean expressions that are deterministic and have no side effects.
- Functions and methods are verified modularly.
- Assertions can be checked with the `assert ASSERTION`


## Quiz
{{#quiz ../quizzes/basic-specs.toml}}

