# Quantifiers and Implication

Programs often deal with data structures of unbounded size, such as linked lists and slices, or with data structures that have a fixed size but are too large to describe point-wise.
For example, let's assume we want to write a function `sort` that takes an array `arr` of type `[1000]int` and returns a sorted array [^1].

``` go
func sort(arr [1000]int) (res [1000]int)
```

If we want to state that the output of this function is sorted, we could write the postcondition `res[0] <= res[1] && res[1] <= .... && res[998] <= res[999]`.
However, this is extremely impractical to write, debug, and maintain.
This section shows how we can use quantifiers to capture these properties concisely.

Gobra supports the universal quantifier `forall`.
The existential quantifier `exists` is available, but its use is discouraged.
Additionally, we introduce the logical operator for the implication (`==>`), which is commonly (but not only) used together with quantifiers.

## Universal quantifier `forall`
To get started, we write an assertion that checks that an array is initialized with zero values:
``` go
~func client1() {
    var a [1000]int
    // @ assert forall i int :: 0 <= i && i < len(a) ==> a[i] == 0
~}
```
We use the `forall` quantifier to use an arbitrary `i` of type `int`.
After the double colons (`::`) follows an assertion that we can use the quantified variable `i`.
Gobra checks that this assertion holds for all instantiations of `i` and reports an error otherwise.

Here, we use an implication (`==>`) [^2] to specify that only if `i` is a valid index (`0 <= i && i < len(a)`), then the element at this index is zero.
All array accesses must be within bounds and in specifications and proof annotations.
Without constraining `i`, the assertion states that `a[i] == 0` holds for all possible integers `i`, which includes amongst others `i=-1` and we face the error:
``` go
~func client2() {
    var a [1000]int
    // @ assert forall i int :: a[i] == 0
~}
```
``` text
ERROR Assert might fail. 
Index i into a[i] might be negative.
```

Returning to the introductory example, let us apply `forall` to write the postcondition of `sort`:
Another way of specifying that an array is sorted is that for any two array elements, the first element must be smaller than or equal to the second element.
So for any integers `i` and `j` with `i < j` it must hold that `res[i] <= res[j]`, again enforcing that the indices `i` and `j` are within bounds:
``` go
// @ ensures forall i, j int :: 0 <= i && i < j && j < len(res) ==> res[i] <= res[j]
func sort(arr [1000]int) (res [1000]int)
```
Note that we can quantify `i` and `j` at the same time instead of using two `forall` quantifiers:
``` go
// @ requires forall i int :: forall j int ::  0 <= i && i < j && j < len(res) ==> res[i] <= res[j]
```

=======
<!--
In general, the syntax
`forall IDENTIFIER [,IDENTIFIER]* T :: ASSERTION` -->

## Efficient verification with triggers
While a universal quantifier states that an assertion holds for all instantiations of a variable, proofs often require knowing the body of a quantifier for concrete instantiations.
Triggers are syntactical patterns that, when matched, trigger Gobra to learn the body of a quantifier with concrete instantiations.
They are crucial for ensuring efficient verification.

Trigger expressions are enclosed in curly braces at the beginning of the quantified expression.
For example, we add `a[i]` as a trigger:
``` gobra
forall i int :: { a[i] } 0 <= i && i < len(a) ==> a[i] == 0`
```
Now when `a[3]` matches `a[i]`, e.g., in `assert a[3] == 0`, Gobra learns the body of the quantifier where `i` is instantiated with `3`:
``` gobra
0 <= 3 && 3 < len(a) ==> a[3] == 0
```

<div class="warning">
While we include triggers in the following examples as a best practice, readers may disregard them for now.
Choosing the right trigger expressions may require careful consideration.
This advanced topic will be addressed in the section on <a href="/triggers.md">triggers</a>.
</div>

## Existential quantifier `exists`
<!-- syntax (`exists IDENTIFIER [,IDENTIFIER]* TYPE :: ASSERTION`). -->
For the existential quantifier, Gobra checks that the assertion holds for _at least one_ instantiation of the quantified variable.

<div class="warning">
Existential quantifiers tend to lead to slow and unpredictable verification times.
As such, we recommend using them sparingly.
Later, we show how we might avoid having to use explicit existential quantifiers through the introduction of ghost state.
</div>
<!-- We can only specify the _existence_ of such a value but do not obtain a witness (an instantiation such that the assertion holds). -->

For completeness, we still show an example:
The function `Contains` returns whether the value `target` is contained in the input array.
We can specify with an implication that if `target` is found, there must exist an index `idx` with `arr[idx] == target`:
``` go verifies
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
Note we can only assert that 10 is contained since there does not exist a `idx` with `arr[idx] = 10`, indirectly `!found` must hold.
To fully capture the intended behavior of `Contains`, the contract should include a postcondition for the case where `target` is not found:
``` go
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
```
So far, we cannot prove this without adding additional proof annotations. <!-- without using [loop invariants](./loops-invariant.md). -->

[^1]: In practice, we may not want to write such a function, as the array must be copied every time we call this function - after all, arrays are passed by value. On another note, the contract of `sort` only specifies that the returned array is sorted. An implementation returning an array full of zeros adheres to this contract. To properly specify `sort`, one should include a postcondition stating that the _multiset_ of elements in the returned array is the same as the multiset of array elements passed to the function.


[^2]: In Gobra the operator for the implication _if P then Q_ is `P ==> Q`.
It has the following truth table:

| `P ==> Q` | `Q=false` | `Q=true` |
|-----------|-----------|----------|
| `P=false` | 1         | 1        |
| `P=true`  | 0         | 1        |
