# Basic Specifications
How can we differentiate between a correct and a faulty implementation?
Before we can prove that a Go program is correct, we must first make it clear _what it means for the program to be correct_.
In this section, we explain how to do this by associating a _contract_ with each function in the program.
The contract for a function has two main components: _preconditions_ and _postconditions_:
Preconditions describe under which conditions a function may be called.
Postconditions describe what conditions hold whenever a function returns.


For example, we give a contract for the function `Abs` that computes the absolute value of a `x int32`. 
Mathematically speaking, `Abs(x)` should return \\( \|x\| \\).
The postcondition `res >= 0 && (res == x || res == -x)` states
that if `x` is negative, it must be negated, and otherwise the same value must be returned.
We could _test_ the expected result for some cases like `Abs(-5) == 5`, `Abs(0) == 0`, and `Abs(1) == 1`, but is this enough?
``` go
//@ ensures res >= 0 && (res == x || res == -x)
func Abs(x int32) (res int32) {
    if x < 0 {
        return -x
    } else {
        return x
    }
}
```
There is a subtle bug, which Gobra detects with [overflow checking](./overflow.md) enabled:
``` text
ERROR Expression -x might cause integer overflow.
```

By two's complement arithmetic there is one more negative integer and negating the smallest `int32` causes overflow: `Abs(-2147483648)` returns `-2147483648` which would clearly violate the postcondition that the result is non-negative.
We complete the contract for `Abs` with a precondition, such that we cannot call `Abs` for this value:
``` go
const MinInt32 = -2147483648  // -1<<32
//@ requires x != MinInt32
//@ ensures res >= 0 && (res == x || res == -x)
func Abs(x int32) (res int32)
```


Gobra uses a _modular_ verification approach.
Each function is verified independently and all we know about a function at call sites is its specification.
This is crucial for scaling verification to large projects.

It is the programmer's job to write the specification, as well as any proof annotations, and it is Gobra's job to check that the proof that a function satisfies its contract is correct.
These checks happen _statically_.
In the next sections, we explain how to prove that a function satisfies its contract and how callers of this function may rely on its contract.


## Preconditions with `requires`
Preconditions are added with the keyword `requires` before a function declaration.
In Go programs, we write Gobra annotations in special line comments starting with `//@`.

> Gobra checks statically that a function's preconditions hold for every call of that function and returns an error if it cannot prove it.

Let us exemplify this with the absolute value example:
``` go
package abs

const MinInt32 = -2147483648

//@ requires x != MinInt32
//@ ensures res >= 0 && (res == x || res == -x)
func Abs(x int32) (res int32) {
    if x < 0 {
        return -x
    } else {
        return x
    }
}

func client1() {
    v1 := Abs(3)  // v1 == 3
    v2 := Abs(-2) // v2 == 2
    v3 := Abs(MinInt32) // error
}

//@ requires a > 0 && b < 0
func client2(a, b int32) {
    v4 := Abs(a)
    v5 := Abs(b) // error
}
```
``` text
ERROR Precondition of call Abs(MinInt32) might not hold. 
Assertion x != -2147483648 might not hold.
ERROR Precondition of call Abs(b) might not hold. 
Assertion x != MinInt32 might not hold.
```

The function `client1` calls `Abs` with constant values.
For the calls `Abs(3)` and `Abs(-2)` the preconditions hold, since clearly `3 != MinInt32` and `-2 != MinInt32`.
This check fails for `Abs(MinInt32)`.
The function `client2` calls `Abs` with its arguments constrained by another precondition `a > 0 && b < 0`.
Here the precondition holds for the call `Abs(a)`, since `a > 0` implies `a != MinInt32`.
We get another error for `Abs(b)`, as the only information about `b` that we have at this point is `b < 0` which does not exclude `b != MinInt32`.


Please note that the errors are reported at the location of the call since the caller is violating the contract of the function.


Preconditions `a > 0 && b < 0` joined by the logical AND can be split into multiple lines.
We can write the contract for `client2` equivalently as:
``` go
//@ requires a > 0
//@ requires b < 0
func client2(a, b int32)
```

## `assert`
Gobra can be instructed to perform checks with the `assert` statement.

> Gobra checks that the assertion holds and reports an error if it cannot prove it.

The first assertion passes in the following program since it can be inferred from the precondition.
``` go
//@ requires a > 0 && b < 0
func client3(a, b int32) {
    //@ assert a > b
    //@ assert b > -10 // error
}
```
``` text
ERROR Assert might fail. 
Assertion b > -10 might not hold.
```

## Postconditions with `ensures`

Postconditions are added with the keyword `ensures` before a function declaration.
By convention, they are written after any preconditions.

> Gobra checks the proof that, the postconditions of a function hold whenever the function returns. Otherwise, an error is reported.

In the absolute value example, we have already added the precondition `res >= 0 && (res == x || res == -x)`.
The comments give the information Gobra has at the respective program locations.
At the begging of the function, we can assume the precondition holds.
Then we get different conditions depending on the branch.
In this example, the postcondition must be proven to hold at both return locations.
With `|=` we write a reasoning steps that lead to the postcondition.
In this case, Gobra can check this automatically.
``` go
const MinInt32 = -2147483648

// @ requires x != MinInt32
// @ ensures res >= 0 && (res == x || res == -x)
func Abs(x int32) (res int32) {
    // x != MinInt32 
    if x < 0 {
        // x != MinInt32 && x < 0
        return -x
        // x != MinInt32 && x < 0 && res == -x
        // |= -x >= 0 && res == -x
        // |= res >= 0 && res == -x
        // |= res >= 0 && (res == x || res == -x)
    } else {
        // x != MinInt32 && !(x < 0)
        return x
        // x != MinInt32 && !(x < 0) && res == x
        // |= x >= 0 && res == x
        // |= res >= 0 && res == x
        // |= res >= 0 && (res == x || res == -x)
    }
}

func client1() {
	v1 := Abs(3)
	//@ assert v1 == 3
	v2 := Abs(-2)
	//@ assert v2 == 2
}
```


## Old Posts
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



## Quiz
{{#quiz ../quizzes/basic-specs.toml}}

