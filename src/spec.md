# Basic specifications

In simple terms, we want to ensure that our functions compute what they should do.

But how do we know their intended functionality?

Example: source code with documentation that has pre/post in plaintext

In this section we introduce the verification of functions with preconditions and postconditions.

if the precondition hold before a call then you can assume the postcondition when the function returns

Together we call the pre and postconditions the specification of the function.

We can view it as a contract between the caller and the callee.

obligation of the caller to satisfy the precondition
and an obligation of the callee to satisfy the postcondition.

It is the programmers job to write the specification
and the Gobra's job to prove whether a function satisfies its specification.

Whenever

`requires`


Example: multiple requires or chain with &&

`ensures`

```gobra
requires x > 0
requires n >= 2 // otherwise counterexample for x==1 and n==1
ensures res > 0
func newton_iteration(x int, n int) (res int) {
	return x/2 + n / x / 2
}
```
[//]: # ( Exercise: find a counterexample )

[//]: # ( chaining the newton iteration (esentially unrolling a loop))


[//]: # ( what the default assertions are)

[//]: # ( what is allowed in an assertion )

```go
func abs(int32 x) {
	return x < 0 ? -x : x
}
```
[//]: # ( a note on overflows )
[//]: # ( post: just >= 0 ? or like a pure function)
[//]: # ( footnote: why int32)

## Modes of failure

### Precondition 
### Postcondition might not hold
### Verifier Timeout
### Order of errors
	<!-- which error do we get first: invariant or postcondition? -->
	<!-- let's test: (yes, reported first) -->
	<!-- invariant false -->
	<!-- for {} -->

```gobra
requires x > 0.0
ensures res > 0.0
func newton_iteration(x float32, n float32) (res float32) {
	return x/2 + n / x / 2
}
```
[//]: # ( explanation? )

## Strength of Conditions

[//]: # ( Quiz: which condition is stronger)

### Problem: overconstraining
[//]: # ( e.g. if they imply false)

## Clients

Whenever a function is called.

Extreme case: `false` as a precondition
