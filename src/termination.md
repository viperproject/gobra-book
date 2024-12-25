# Termination

Having talked about loops, the next thing to address is termination.
Here we look at the termination of loops and recursive functions.
In general, this problem is a hard problem[^1].
However, for functions we write in practice, it is usually not hard to show termination.
Informally it is often clear to argue for (non-)termination.
Sometimes, we might even desire non-termination for some functions,
e.g. a web server that continuously serves requests.


## Partial and Total Correctness

By default, Gobra does not check for termination and proves only *partial correctness*.
For functions, this means that if a function terminates its postcondition can be asserted.
*Total correctness* additionally requires termination.

For example, the following program verifies even though `infiniteZero` contains an infinite loop.
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
This behavior is intended since the verifier checks that
1. assuming that `infiniteZero` terminates then the postcondition `res == 0` holds.
2. While never reached in practice, the assertion `r == 0` should also hold since the client can deduce this from the postcondition.

## Termination Measures and `decreases`
We can instruct Gobra to check for termination by adding the `decreases` keyword to the specification of a function or a loop. It must come after the `invariant`s.
Sometimes, this suffices and a termination measure can be automatically inferred.
For example, for simple functions like:
``` go
decreases
func Abs(x int) (res int) {
    if x < 0 {
       return -x 
    } else {
       return x
    }
}
```

In other cases, we need to provide a *termination measure*.
A termination measure is an expression that must
- be lower-bounded
- decrease

For functions, it must decrease for every recursive invocation.
Respectively for loops, it must decrease for every iteration.

What it means to be lower-bounded and to be decreasing is defined by Gobra for different types.
For example, integers `i, j int` are lower-bounded if `i >= 0` and decreasing if `i < j`.

A common case is that we iterate over an array with an increasing loop variable `i`.
We can easily construct a termination measure that decreases instead by subtracting `i` from the array's length.
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
Let us look again at the [binary search](./loops-binarysearch.md) example.
This time we introduce an implementation error:
`low` is updated as `low = mid` instead of `low = mid + 1`.
`BinarySearchArr` could loop forever, for example for `BinarySearchArr([7]int{0, 1, 1, 2, 3, 5, 8}, 8)`.
Without `decreases` the function would still verify since only partial correctness is checked.
<!-- 
For example for `N=3`, `BinarySearchArr([N]int{1, 2, 3}, 2)` does not terminate.
	arr := [N]int{1, 2, 3}
	i := BinarySearchArr(arr, 2)
low mid high
 0 1 3
 1 1 2
    -->
``` go
// @ decreases
// @ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < N ==> arr[i] <= arr[j]
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != value
func BinarySearchArr(arr [N]int, value int) (found bool) {
	low := 0
	high := len(arr) - 1
	mid := 0
	//@ invariant 0 <= low && low <= high && high < len(arr)
	//@ invariant 0 <= mid && mid < len(arr)
	//@ invariant forall i int :: {arr[i]} 0 <= i && i < low ==> arr[i] < value
	//@ invariant forall i int :: {arr[i]} high < i && i < len(arr) ==>  value < arr[i]
	//@ decreases high - low
	for low < high {
		mid = (low + high) / 2
		if arr[mid] == value {
			return true
		} else if arr[mid] < value {
			low = mid // <--- Implementation Error, should be low=mid+1
		} else {
			high = mid
		}
	}
	return arr[low] == value
}
```
``` sh
ERROR Function might not terminate. 
Required termination condition might not hold.
```

We might be tempted to try `decreases high` or `decreases len(arr)-low` as termination measures for the loop.
However, this is not enough since the termination measure must decrease in every iteration.
In iterations where we update `low`, `high` does not decrease, and vice versa.
The solution is to combine the two as `decreases high - low`.
This measure coincides with the length of the subarray that has not been searched yet.
If we change back to `low=mid+1`, the program verifies again .


## Wildcard Termination Measure `_`
If we annotate a function or method with `decreases _`, termination is assumed and not checked.

The wildcard termination measure `_` should be used carefully, especially in conjunction with `pure` functions.
Contradictions can arise if we specify that a function terminates that does not terminate.

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
Then assertion verifies since the postcondition of `infiniteRecursion` establishes `false` from which we can prove any assertion, including logical inconsistencies like `0 != 1`.


The use of the wildcard measure can be justified when termination is proven by other means, for example leveraging a different tool.
Another use case is *Gradual Verification*.

## Full Syntax
`"decreases" [expressionList] ["if" expression]`

### Decreases Tuple
Sometimes, it might be hard to find a single expression that decreases.
In general, one can specify a list of expressions with
`decreases E1, E2, ..., EN`.

A tuple termination measure decreases based on the lexicographical order over the tuple elements.

For `BinarySearchArr` we used `decreases high - low`.
Alternatively, we could use `decreases high, len(arr) - low`

### Conditional 
When we want to prove termination only under certain conditions we can add an `if` clause at the end.

One is allowed to add only a single clause per kind of termination measure (tuple or wildcard).
But we can have a clause for a tuple termination measure while using the wildcard termination measure in other cases.
But when the condition held for a tuple measure, this same measure must decrease for all further recursive invocations and can not *downgrade* to a wildcard measure.

## Mutual Recursion
Gobra can also handle termination for mutual recursive functions.
For them, the termination measure must decrease for each indirect call.


## Quiz

{{#quiz ../quizzes/termination.toml}}

## Summary
- By default, Gobra checks for partial correctness.
- For a *naked* `decreases`, Gobra attempts to prove termination automatically.
- `decreases _` assumes termination, `_` is called the wildcard termination measure.

In the next section, we discuss why `pure` and `ghost` functions must have termination measures.

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

[^1]: The problem of whether a function terminates is known as the
[Halting Problem](https://en.wikipedia.org/wiki/Halting_problem).
and is not merely hard but undecidable.
