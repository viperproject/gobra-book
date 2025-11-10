# Termination

Having discussed loops, the next thing to address is termination.
Here, we look at the termination of loops and recursive functions.
In general, proving termination is [undecidable](https://en.wikipedia.org/wiki/Halting_problem).
However, for functions we write in practice, it is usually not hard to show termination.
By default, Gobra checks for _partial correctness_, i.e., correctness with respect to specifications _if the function terminates_.
For _total correctness_, both termination and correctness with respect to specifications must be proven.
Gobra uses _termination measures_, i.e., expressions that are strictly decreasing and bounded from below to prove termination.


## Partial correctness
Let us explore the concept of partial correctness further.
The function `infiniteZero` contains an infinite loop, so it will not terminate.
It is still partially correct with respect to its contract since the postcondition `false` must only be proven to hold when it returns, which it does not.

``` go verifies
// @ ensures false
func infiniteZero() (res int) {
    for {}
    return 0
}

func main() {
    r := infiniteZero()
    // @ assert r == 1
}
```
When the function `main` is verified, whether `infiniteZero` terminates is unknown.
However, the contract guarantees that when `infiniteZero` returns, its postcondition holds.
Assuming it terminates, we can assert an arbitrary property, such as `r == 1`.
This is fine since this statement will never be reached if we run the program.

## Specifying termination measures with `decreases`
We can instruct Gobra to check for termination by adding the `decreases` keyword to the specification of a function or a loop.
It must come right before the function/loop after any preconditions/postconditions/invariants.
Sometimes, this suffices, and a termination measure can be automatically inferred. 
For example, for simple functions like `Abs` that terminate immediately:
``` go verifies
// @ decreases
func Abs(x int) (res int) {
    if x < 0 {
       return -x 
    } else {
       return x
    }
}
```

In other cases, we need to provide a termination measure.
A termination measure must be
- lower-bounded
- decrease

For functions, it must decrease for every recursive invocation.
Respectively for loops, it must decrease for every iteration.

What it means to be lower-bounded and to be decreasing is defined by Gobra for different types.
For example, integers `i, j int` are lower-bounded if `i >= 0` and decreasing if `i < j`.

## Termination of loops
A common case is that we iterate over an array with an increasing loop variable `i`, as seen in the function `LinearSearch`.
We can construct a termination measure that decreases instead by subtracting `i` from the array's length.
``` go verifies
// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
// @ decreases
func LinearSearch(arr [10]int, target int) (idx int, found bool) {
    // @ invariant 0 <= i && i <= len(arr)
    // @ invariant forall j int :: 0 <= j && j < i ==> arr[j] != target
    // @ decreases len(arr) - i
    for i := 0; i < len(arr); i += 1 {
        if arr[i] == target {
            return i, true
    }
    }
   return -1, false
}

// @ decreases
func client() {
    arr := [10]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
    i10, found := LinearSearch(arr, 10)
    // @ assert !found
    // @ assert forall i int :: 0 <= i && i < len(arr) ==> arr[i] != 10
    // @ assert arr[4] == 4
    i4, found4 := LinearSearch(arr, 4)
    // @ assert found4
    // @ assert arr[i4] == 4
}
```
We can also prove that `client` terminates since, except for the calls to `LinearSearch`, which terminate, there is no diverging control flow.
If we do not specify a termination measure `decreases len(arr) - i` for the loop, Gobra reports the error:
``` text
ERROR Function might not terminate. 
Required termination condition might not hold.
```

## Termination of recursive functions
The function `fibonacci` recursively computes the `n`'th iterate of the Fibonacci sequence.
As a termination measure, the parameter `n` is suitable since we recursively call `fibonacci` with smaller arguments and `n` is bounded from below.
``` go verifies
// @ requires n >= 0
// @ decreases n
func fibonacci(n int) int {
    if n <= 1 {
        return n
    } else {
        return fibonacci(n-1) + fibonacci(n-2)
    }
}
```

Verification fails if we mistype `buggynacci(n-0)` instead of `buggynacci(n-1)`.
``` go does_not_verify
// @ requires n >= 0
// @ decreases n
func buggynacci(n int) int {
    if n == 0 || n == 1 {
        return n
    } else {
        return buggynacci(n-0) + buggynacci(n-2)
    }
}
```
``` text
ERROR Function might not terminate. 
Termination measure might not decrease or might not be bounded.
```

## Assuming termination with `decreaes _`
If we annotate a function or method with `decreases _`, termination is assumed and not checked.

This can be dangerous. With the termination measure `_`, we can assume that `buggynacci` terminates.
Then the following program verifies where we want to prove that the `client` code terminates.
In practice, `buggynacci` would never return, and `doSomethingVeryImportant` would never be called.
``` go
~// @ decreases
~// @ func doSomethingVeryImportant()
~
// @ requires n >= 0
// @ decreases _
func buggynacci(n int) int {
    if n == 0 || n == 1 {
        return n
    } else {
        return buggynacci(n-0) + buggynacci(n-2)
    }
}

// @ decreases
func client() {
    x := buggynacci(n) 
    doSomethingVeryImportant()
}

```
The use of the wildcard measure can be justified when termination is proven by other means, such as leveraging a different tool.
Another use case is _gradual verification_ where it can be useful to assume termination of functions in a codebase, that have not yet been verified.

<!-- Full Syntax `"decreases" [expressionList] ["if" expression]` -->


## Termination of binary search
Let us look again at the [binary search](./loops-binarysearch.md) example.
This time, we introduce an implementation error:
`low` is updated to `low = mid` instead of `low = mid + 1`.
`BinarySearchArr` could loop forever, for example, with `BinarySearchArr([7]int{0, 1, 1, 2, 3, 5, 8}, 8)`.
The function would still verify without `decreases` since only partial correctness is checked.
<!-- 
For example for `N=3`, `BinarySearchArr([N]int{1, 2, 3}, 2)` does not terminate.
	arr := [N]int{1, 2, 3}
	i := BinarySearchArr(arr, 2)
low mid high
 0 1 3
 1 1 2
    -->
``` go does_not_verify
// @ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
// @ ensures 0 <= idx && idx <= len(arr)
// @ ensures idx > 0 ==> arr[idx-1] < target
// @ ensures idx < len(arr) ==> target <= arr[idx]
// @ ensures found == (idx < len(arr) && arr[idx] == target)
// @ decreases  // <--- added for termination checking
func BinarySearchArr(arr [N]int, target int) (idx int, found bool) {
    low := 0
    high := len(arr)
    mid := 0
    // @ invariant 0 <= low && low <= high && high <= len(arr)
    // @ invariant 0 <= mid && mid < len(arr)
    // @ invariant low > 0 ==> arr[low-1] < target
    // @ invariant high < len(arr) ==> target <= arr[high]
    // @ decreases high - low   // <-- added for termination checking
    for low < high {
        mid = (low + high) / 2
        if arr[mid] < target {
            low = mid // <--- Implementation Error, should be low=mid+1
        } else {
            high = mid
        }
    }
    return low, low < len(arr) && arr[low] == target
}

```
``` sh
ERROR Function might not terminate. 
Required termination condition might not hold.
```

We might be tempted to try `decreases high` or `decreases len(arr)-low` as termination measures for the loop.
However, this is insufficient since the termination measure must decrease every iteration.
In iterations where we update `low`, `high` does not decrease, and vice versa.
The solution is to combine the two as `decreases high - low`.
This measure coincides with the length of the subarray that has not been searched yet.
If we change back to `low=mid+1`, the program verifies again.


## Decreases tuple
Sometimes, it might be hard to find a single expression that decreases.
Generally, one can specify a list of expressions with `decreases E1, E2, ..., EN`.

A tuple termination measure decreases based on the [lexicographical order](https://en.wikipedia.org/wiki/Lexicographic_order) of the tuple elements.

For `BinarySearchArr`, we used `decreases high - low`.
Alternatively, we could use:
``` go
// @ decreases high, len(arr) - low
```

## TODO Conditional termination with `if` clauses
<!--
When we want to prove termination only under certain conditions, we can add an `if` clause at the end.

One can only add a single clause per kind of termination measure (tuple or wildcard).
However, we can have a clause for a tuple termination measure while using the wildcard termination measure in other cases.
But when the condition held for a tuple measure, this measure must decrease for all further recursive invocations and cannot *downgrade* to a wildcard measure. -->
<!-- TODO proper example -->

## TODO Mutual recursive functions
<!-- Gobra can also handle termination for mutual recursive functions. -->
<!-- For them, the termination measure must decrease for each indirect call. -->
<!-- TODO proper example -->


<!-- 
> By default, Gobra checks for partial correctness.
>
> Termination is proven when `decreases` is specified.
>
> `decreases _` assumes termination
> A *naked* `decreases` is equivalent to `decreases 0`, i.e., ... -->


{{#quiz ../../quizzes/termination.toml}}


