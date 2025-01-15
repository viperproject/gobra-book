# Quantifiers and Implication

Gobra supports the universal quantifier `forall`.
The existential quantifier `exists` is available , but its use is discouraged.
Additionally, we  introduce the logical operator for implications (`==>`), which is commonly used with quantifiers.

<!-- without trigger `forall IDENTIFIER [,IDENTIFIER]* T :: ASSERTION` -->
To get started, we write an assertion that checks that an array is initialized with zero values.
``` go
~const N = 42
~func client1() {
    var a [1000]int
    // @ assert forall i int :: 0 <= i && i < len(a) ==> a[i] == 0
~}
```
We make use of the `forall` quantifier to use an arbitrary `i` of type `int`.
After double columns (`::`) follows an assertion in which we can use the quantified variable `i`.
Gobra checks that this assertion holds for all instantiations of `i` and reports an error otherwise.
Here we use an implication[^1] to specify that only if `i` is a valid index (`0 <= i && i < len(a)`), then the element at that index is zero.

Array indices must also be in bounds for specifications.
Without constraining `i`, Gobra must check that `a[i] == 0` holds for all possible integers.
This could include `i=-1` and we face the error:
``` go
~const N = 42
~func client2() {
    var a [N]int
    // @ assert forall i int :: a[i] == 0
~}
```
``` text
ERROR Method contract is not well-formed. 
Index i into arr[i] might be negative.
```

## Triggers
Quantifiers can complicate efficient verification.
To reduce the work of the underlying solver, we can specify trigger expressions that determine when a quantified assertion is instantiated.
Trigger expressions are enclosed in curly braces. 
For example, we add `a[i]` as a trigger to:
`forall i int :: { a[i] } 0 <= i && i < len(a) ==> a[i] == 0`.

> While we include triggers in the following example as a best practice, readers may disregard them for now.
> Choosing the right trigger expressions may require careful consideration.
> This advanced topic will be addressed in the section on [triggers](./triggers.md).


## Example: Sorted Array
Let us write an assertion that states that an array is sorted.
We can later use this as a precondition for a  [binary search](./loops-binarysearch.md) function.
As a first attempt, we might write something along the lines of
`requires arr[0] <= arr[1] <= arr[2] <= ... <= arr[N-1]`
Of course, we do not want to write specifications like this since this does not scale and would not work for different lengths `N`.

Another way of specifying that an array is sorted
is that for any two array elements,
the first element must be less than or equal to the second element.
We cannot directly pick any two elements,
but we can state that for any indices `i` and `j` it must hold `arr[i] <= arr[j]`.
Again, we must enforce that `i` and `j` are valid indices.
This results in the precondition:
``` go
// @ ensures forall i, j int :: {res[i], res[j]} 0 <= i && i < j && j < len(res) ==> res[i] <= res[j]
func sort(arr [1000]int) (res [1000]int)
```
Note that we can quantify `i` and `j` at the same time instead of using two `forall` quantifiers:
`requires forall i int :: forall j int :: arr[i] <= arr[j]`.

<!-- conceptual:
Note that this is very powerful:
For example for `forall i int64 :: P`
P has to hold for all of the \\(2^64\\) possible values for i
Testing all of those values is already infeasible.
 -->
<!--
In general, the syntax
`forall IDENTIFIER [,IDENTIFIER]* T :: ASSERTION` -->

## Existential Quantifier `exists`
The existential quantifier `exists` uses similar syntax (`exists IDENTIFIER [,IDENTIFIER]* TYPE :: ASSERTION`).
Gobra checks, that the assertion holds for _at least one_ instantiation.
It can be a heavy burden for the verifier to prove this.
We can only specify the _existence_ of such a value but do not obtain a witness (an instantiation such that the assertion holds).
Hence `exists` should be avoided.
Later we show how `ghost` variables or parameters can be used as an efficient alternative.

For completeness, we still show an example.
The function `Contains` performs returns whether the value `target` is contained in the input array.
We can specify that when `target` is found there must exist an index `idx` with `arr[idx] == target`:
``` go
// @ ensures found ==> exists idx int :: 0 <= idx && idx < len(arr) && arr[idx] == target
func Contains(arr [10]int, target int) (found bool) {
    for i := range arr {
        if arr[i] == target {
            return true
        }
    }
    return false
}

func client3() {
    arr := [10]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
    found := Contains(arr, 10)
    // @ assert !found
    found4 := Contains(arr, 4)
}
```
Note we can only assert that 10 is contained.
Indirectly, since there does not exist a `idx` with `arr[idx] = 10`, `!found` must hold.
The contract would need a postcondition for the case where `target` is not found.
So far we cannot show this without loop invariants.

<!-- indirectly -->

## Footnotes
[^1]: In Gobra the operator for the implication _if P then Q_ is `P ==> Q`.
It has the following truth table:

| `P ==> Q` | `Q=false` | `Q=true` |
|-----------|-----------|----------|
| `P=false` | 1         | 1        |
| `P=true`  | 0         | 1        |


Note that if `P` is `false`, `P ==> Q` holds independent of whether `Q` holds.
In the above example we had
`forall i int :: 0 <= i && i < len(a) ==> a[i] == 0`.
So whenever `i` is not a valid index then the entire assertion holds.

<!-- `forall i int :: 0 <= i && i < len(a) && a[i] == 0` -->
