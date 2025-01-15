# Basic Specifications
How can we differentiate between a correct and a faulty implementation?
Before we can prove that a Go program is correct, we must first make it clear _what it means for the program to be correct_.
In this section, we explain how to do this by associating a _contract_ with each function in the program.
The contract for a function has two main components: _preconditions_ and _postconditions_:
Preconditions describe under which conditions a function may be called.
Postconditions describe what conditions hold whenever a function returns.


For example, the function `Abs` should compute the absolute value of a `x int32`. 
Mathematically speaking, `Abs(x)` should return \\( \|x\| \\).
``` go
// ##(--overflow)

// @ ensures res >= 0 && (res == x || res == -x)
func Abs(x int32) (res int32) {
    if x < 0 {
        return -x
    } else {
        return x
    }
}
```
This function is annotated with a contract. Contracts may be added to functions via comments that start with the marker `// @` or that are in between markers `/*@` and `@*/` for multi-line annotations, and they must be placed immediately before the function signature.
The contract for `Abs` contains a single postcondition, marked with the `ensures` keyword, but it may contain more than one.
Contracts may also be annotated with multiple preconditions, marked with the `requires` keyword, as we shall exemplify later.
The postcondition `res >= 0 && (res == x || res == -x)` states
that if `x` is negative, it must be negated, and otherwise the same value must be returned.

To make sure this function is correct, one could test it by writing unit tests, for various inputs. Unfortunately, it is very easy to ignore corner cases when writing tests.
There is a subtle bug, which Gobra detects with [overflow checking](./overflow.md) enabled:
``` text
ERROR Expression -x might cause integer overflow.
```
<div class="warning">
Overflow checking is still experimental and under implementation, and because of that, it is disabled by default.
It can be enabled with the option <code>--overflow</code> in the CLI, or with the annotation <code>// ##(--overflow)</code> in the beginning of a file.
</div>

Without this option, Gobra would accept the function `Abs`.

Go uses [two's complement arithmetic](https://en.wikipedia.org/wiki/Two's_complement), so the minimum signed integer that can be represented with 32 bits is `-2147483648`, whereas the maximum is `2147483647`. Because of this, the computation of the `Abs` of the minimum integer overflows.
<!-- https://pkg.go.dev/math -->
<!-- `Abs(-2147483648)` returns `-2147483648`  -->

We complete the contract for `Abs` with a precondition that prevents `Abs` from being called with `MinInt32` as its argument.
``` go
// ##(--overflow)
const MinInt32 = -2147483648  // -1<<32

// @ requires x != MinInt32
// @ ensures res >= 0 && (res == x || res == -x)
func Abs(x int32) (res int32)
```
Gobra only considers function calls that satisfy the precondition.
That is why we are able to prove that the postcondition holds by adding this precondition.

It is the programmer's job to specify the functions they write and to provide any annotations that may guide the proof (more on this later).
In turn, Gobra checks that all function contracts hold and that the function will never panic (for example, due to a division by zero).
If the program fails to verify, Gobra produces helpful error messages that can help to identify the error.
These checks happen statically before the program is even compiled.
**These annotations do not impose any runtime checks, and thus, they do not introduce any changes in the program's behavior or performance**.
In the next sections, we explain how to prove that a function satisfies its contract and how callers of this function may rely on its contract.


## Specifying preconditions with `requires` clauses
Preconditions are added with the keyword `requires` before a function declaration.
For any reachable call, Gobra checks whether the function's precondition is guaranteed to hold.
Since this is enforced, the precondition can be assumed to hold at the beginning of a function.
Let us exemplify this with the absolute value example:
```go
const MinInt32 = -2147483648

// @ requires x != MinInt32
// @ ensures res >= 0 && (res == x || res == -x)
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

// @ requires a > 0 && b < 0
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
We get another error for `Abs(b)`, as the only information Gobra has about `b` at this point is `b < 0` which does not exclude `b != MinInt32`.

Please note that the errors are reported at the location of the call since the caller is violating the contract of the function.

<!-- actually, it is a "separating conjunction" -->
Preconditions `a > 0 && b < 0` joined by the logical AND can be split into multiple lines.
We can write the contract for `client2` equivalently as:
```go
// @ requires a > 0
// @ requires b < 0
func client2(a, b int32)
```

> Gobra checks that a function's preconditions hold for every call of that function and reports an error if it cannot prove it.
>
> Gobra assumes the preconditions hold at the beginning of the function's body.

## Proof annotation: `assert` statements
Before we look at postconditions, we introduce our first kind of proof annotation: `assert` statements.
These statements check whether some condition is guaranteed to hold on all program paths that reach it.
Because of this, it may be very useful when constructing and debugging proofs, as we shall see throughout this book.
As with any other annotations introduced by Gobra, they must occur in comments marked with `// @`.
Once again, notice that Gobra verifies programs before they are even compiled.
These checks do not introduce any assertions at runtime, so there is no performance cost to adding these annotations.

The first assertion passes in the following program since it can be inferred from the precondition.
```go
// @ requires a > 0 && b < 0
func client3(a, b int32) {
    // @ assert a > b
    // @ assert b > -10 // error
}
```
``` text
ERROR Assert might fail. 
Assertion b > -10 might not hold.
```

> For an `assert` statement, Gobra statically checks that the assertion holds and reports an error if it cannot prove it.

## Specifying postconditions with `ensures` clauses

Postconditions are added with the keyword `ensures` before a function declaration.
By convention, they are written after any preconditions.
In the contract of the function `Abs`, we have already seen the postcondition `res >= 0 && (res == x || res == -x)`.

When a function is called, Gobra checks that its preconditions hold at the call site, and if so, the postcondition is assumed.
We illustrate this by adding `assert` statements in the code for `client4` that show that the postcondition of `Abs` holds.
```go
const MinInt32 = -2147483648

// @ requires x != MinInt32
// @ ensures res >= 0 && (res == x || res == -x)
func Abs(x int32) (res int32) {
    // @ assert x != MinInt32
    if x < 0 {
        // @ assert x != MinInt32 && x < 0
        return -x
    } else {
        // @ assert x != MinInt32 && !(x < 0)
        return x
    }
}

func client4() {
    v1 := Abs(3)
    // @ assert v1 >= 0 && (v1 == 3 || v1 == -3)
    // @ assert v1 == 3
    v2 := Abs(-2)
    // @ assert v2 >= 0 && (v2 == -2 || v2 == -(-2))
    // @ assert v2 == 2
}
```

At the beginning of the function `Abs`, the precondition holds.
Then depending on the branch taken, different constraints hold for `x`.
After the call to `Abs`, we can `assert` the postcondition (with the arguments substituted, for example, `v2 >= 0 && (v2 == -2 || v2 == -(-2))` implies that `v2 == 2` which can also be asserted).

Gobra uses a _modular_ verification approach.
Each function is verified independently and all we know about a function at call sites is its contract.
This is crucial for scaling verification to large projects.


If we exchange the bodies of the `if` statement, the function `WrongAbs` does not satisfy its contract:
``` go
const MinInt32 = -2147483648

// @ requires x != MinInt32
// @ ensures res >= 0 && (res == x || res == -x)
func WrongAbs(x int32) (res int32) {
    if x < 0 {
        return x
    } else {
        return -x
    }
}
```
``` text
ERROR Postcondition might not hold. 
Assertion res >= 0 might not hold.
```

> Gobra checks that a function's postconditions hold whenever the function returns and reports an error if it cannot prove it.

## Default precondition and postcondition
A `requires` or `ensures` clause may be omitted from a contract, or both clauses may be omitted. In such cases, the precondition and postcondition default to `true`.
``` go
func foo() int
```
is equivalent to
``` go
// @ requires true
// @ ensures true
func foo() int
```

Since `true` always holds, the precondition `true` does not restrict when a function can be called.
A postcondition `true` provides no information about the return values.

> If no precondition is specified by the user, it defaults to `true`.
>
> If no postcondition is specified by the user, it defaults to `true`.

## Quiz
{{#quiz ../quizzes/basic-specs.toml}}

