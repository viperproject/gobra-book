# Quantifiers and Implication

Let us try to write an assertion that states that an array is sorted.
We can later use this as a precondition for a  [binary search](./loops-binarysearch.md) function.
As a first attempt we might write
`requires arr[0] <= arr[1] <= arr[2] <= ... <= arr[N-1]`
Of course, we do not want to write specifications like this since this does not scale and would not work for different lengths `N`.

Another way of specifying that an array is sorted
is that for any two elements of the array,
the first element must be less than or equal to the second element.

## Universal quantifier `forall`
In Gobra, *for any* is realized by the `forall` quantifier.
We cannot directly pick any two elements,
but we can state that for any indices `i` and `j` of type `int`, `arr[i] <= arr[j]` as
`requires forall i, j int :: arr[i] <= arr[j]`
Note that we can quantify `i` and `j` at the same time, 
 instead of the more cumbersome
`requires forall i int :: forall j int :: arr[i] <= arr[j]`

Array indices must also be in bounds for specifications.
We need to constrain that `i` and `j` are valid indices, otherwise, we see errors like:
``` text
Method contract is not well-formed. 
Index i into arr[i] might be negative.
```

## Implication `==>`
In Gobra the operator for the implication[^1]  *if P then Q* is `==>`.
This gives our final version for the precondition:

```gobra
requires forall i, j int :: 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
func search(arr [N]int)
```

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
The existential quantifier `exists` uses the same syntax (`exists IDENTIFIER [,IDENTIFIER]* T :: ASSERTION`).
As the name suggests, `exists` requires the assertion to be true for *at least one* value.

For example, we could state `arr` contains the value `0` as
``` gobra
exists i int :: 0 <= i && i < len(arr) ==> arr[i] == 0
```

`exists` should be used sparingly.
It can be a heavy burden for the verifier to find a witness among many possible values.
We show later how we could use a `ghost` return value instead.

## Footnotes

[^1]: The implication operator has the following truth table:

| `P ==> Q` | `Q=false` | `Q=true` |
|-----------|-----------|----------|
| `P=false` | 1         | 1        |
| `P=true`  | 0         | 1        |
