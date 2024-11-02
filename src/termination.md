# Termination

Having talked about loops, the next thing to address is termination.
Here we look at termination of loops and recursive functions.
<!-- or goto, deadlock, ...  -->
In general this problem is a hard problem[^1].
But for functions that we write in practice it is usually not hard to show termination.
Informally it is often clear to argue for (non-)termination.
In some cases, we might even desire non-termination for some functions,
e.g. a web server that continuously serves requests.

<!-- By finding a property that decreases -->
<!-- could not not check due to bug  -->
<!-- https://github.com/viperproject/gobra/issues/783 -->
<!-- ``` go -->
<!-- // @ decreases -->
<!-- func main() { -->
<!-- 	i := 0 -->
<!-- loop: -->
<!-- 	i++ -->
<!-- 	goto loop -->
<!-- } -->
<!-- ``` -->
<!-- By viper, this would still be considered a loop -->

## Partial and Total Correctness

By default Gobra does not check for termination and proves only *partial correctness*.
For functions, this means that if a function terminates its postcondition can be asserted.
*Total correctness* additionally requires termination.

<!-- stupid example -->
For example the following program verifies even though `infiniteZero` contains an infinite loop.
```gobra
ensures res == 0
func infiniteZero() (res int) {
    for {}
    return 0
}
func client() {
    r := infiniteZero()
    assert r == 0
}
```
This is behavior is intended since the verifier checks that
1. assuming that `infiniteZero` terminates then the postcondition `res == 0` holds.
2. While never reached in practice, the assertion `r == 0` should also hold since client can deduce this from the postcondition.

## Termination Measures and `decreases`
We can instruct Gobra to check for termination by adding the `decreases` keyword to the specification of a function or a loop.

In some cases this suffices
and a termination can be automatically inferred.


In other cases we need to provide a *termination measure*.

A termination measure is an expression that must be lower bounded and
- for functions it must decrease for every recursive invocation
- respectively for loops it must decrease for every iteration

<!-- TODO lower bounded by what exactly -->
<!-- TODO decreases N - i - 10 "...might not be bounded" -->
<!-- TODO but this works? decreases N - i - 2 -->
<!-- but not  decreases N - i - 3 -->

A common case is that we iterate over an array where a loop variable `i` increases.
We can easily construct a termination measure that decreases instead by subtracting `i` from the length of the array.
``` go
	//@ decreases len(arr) - i
	for i:=0; i<N; i++ {
		if arr[i] > res {
			res = arr[i]
			idx = i
		}
	}
```

## Binary Search Termination
Let us look again at the binary search example.
We might forget to add one and update `low = mid` instead of `low = mid + 1`.
``` go
    mid = (high-low)/2 + low
    if arr[mid] <= value {
        low = mid
    } else {
        high = mid
    }
```
For example for `N=3`, `bisectRight([N]int{1, 2, 3}, 2)` does not terminate.
But the program still verifies since only partial correctness is checked.
<!-- 
	arr := [N]int{1, 2, 3}
	i := bisect_right(arr, 2)
low mid high
 0 1 3
 1 1 2
    -->
This changes when we add `decreases`.
``` go
// @ decreases
func bisect_right(arr [N]int, value int) (idx int) {
```
``` sh
Error at: </home/gobra/bisect.go:68:2> Function might not terminate. 
Required termination condition might not hold.
```
If we fix the error and change the update back to `low = mid + 1` we still get the same error.
That is due to the loop for which we have to specify a termination measure as well.

<!-- must be after invariants -->

We might be tempted to try `decreases high` or `decreases N-low` as termination measures.
But this is not enough since the termination measure must decrease in every iteration. In iterations where we update `low`, `high` does not decrease and vice versa.

The solution is to combine the two as `decreases high - low`.
It can be helpful to think of the interpretation for the algorithm.
In this case `high - low` denotes the length of the subarray that we have not checked yet.

Now the program verifies again.


<!-- In this case we have to manually find the termination measure as Gobra cannot infer it. -->
<!-- ``` go -->
<!-- //@ invariant ... -->
<!-- //@ decreases -->
<!-- for low < high { -->
<!--     mid = (high-low)/2 + low -->
<!--     if arr[mid] <= value { -->
<!--         low = mid + 1 -->
<!--     } else { -->
<!--         high = mid -->
<!--     } -->
<!-- } -->
<!-- ``` -->

<!-- ``` sh -->
<!-- The loop decreases might not terminate.  -->
<!-- Termination measure might not decrease or might not be bounded. -->
<!-- ``` -->



## Pure and Ghost Functions
All `pure` and `ghost` functions and methods must have termination measures.

``` gobra
requires n >= 0
decreases n
pure
func fib(n int) (ghost res int) {
    return n <= 1 ? n : fib(n-1) + fib(n-2)
}
```

<!--  ``` sh -->
<!-- error: All pure or ghost functions and methods must have termination measures, but none was found for this member. -->
<!--  ``` -->
  
<!-- ``` gobra -->
<!-- ghost -->
<!-- decreases n -->
<!-- requires n >= 0 -->
<!-- func fibonacci(n int) int { -->
<!-- 	if n <= 1 { -->
<!--        return n -->
<!--     } else { -->
<!--        return fibonacci(n-1) + fibonacci(n-2) -->
<!--     } -->
<!-- } -->
<!-- ``` -->

## Wildcard Termination Measure `_`
If we annotate a function or method with `decreases _`, termination is assumed and not checked.

The wildcard termination measure `_` should be used with care, especially in conjunction with `pure` functions.
Contradictions can arise if we specify that that a function terminates that does in fact not terminate.

``` gobra
decreases _
ensures false
pure
func infiniteRecursion() {
	infiniteRecursion()
	assert 0 != 1
}
```
Because of the wildcard measure the verifier assumes that `infiniteRecursion` terminates.
Then assertion verifies since the postcondition of `infiniteRecursion` establishes `false` from which we can prove any assertion, also including logical inconsistencies like `0 != 1`.


Use of the wildcard measure can be justified when termination is proved by other means, for example leveraging a different tool.
Another usecase is *Gradual Verification*.

## Full Syntax
`"decreases" [expressionList] ["if" expression]`

### Decreases List
In some cases it might be hard to find a single expression that decreases.
In general specify a list of expressions
`decreases E1, E2, ..., EN`.

<!-- TODO exlain lexicographic order -->
<!-- in general, we don't have only ints -->

For `bisectRight` we used `decreases high - low`.
Alternatively we could use `decreases high, N - low`
<!-- Ackermann example? -->

### Conditional 
When we want to proof termination only under certain conditions we can add an `if` clause at the end.

<!-- Viper tutorial: To ensure soundness, only a *single* clause per kind of measure is allowed. Moreover, it is not allowed to "downgrade" from a tuple to a wildcard: if ``'s condition held in the call's prestate, then `` must decrease, even if the wildcard condition holds at a recursive call -->

## Mutual Recursion




{{#quiz ../quizzes/termination.toml}}

## Summary
- By default, Gobra checks for partial correctness.
- For a *naked* `decreases`, Gobra tries to automatically prove termination.
- `decreases _` assumes termination, it is called the wildcard termination measure.
- `pure` and `ghost` functions must have a termination measure to be well-defined.


## Background
If you could find a termination measure for the function `Collatz` you would solve a
[famous mathematical problem](https://en.wikipedia.org/wiki/Collatz_conjecture).
``` go
//@ requires n >= 1
func Collatz(n int) int {
    if n == 1 {
        return 1
    } else if n % 2 == 0 {
        return Collatz(n / 2)
    } else {
        return Collatz(3 * n + 1)
    }
}
```

[^1]: The problem whether a function terminates is known as the
[Halting Problem](https://en.wikipedia.org/wiki/Halting_problem).
and is not merely hard but undecidable.
