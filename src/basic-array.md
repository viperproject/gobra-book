# Array Operations
<!--
explain preconditions of an indexing operation, make it clear that accesses out of bounds are excluded statically -->

In this chapter we operate with arrays of fixed size `N`.
Later we will also look at slices.
Note that the array `arr` is passed by value and therefore copied.

Go can find out of bounds indices for constant values when compiling a program.
``` go
package main
import "fmt"
func main() {
	a := [5]int{2, 3, 5, 7, 11}
	fmt.Println(a[-1]) // invalid index (too small)
	fmt.Println(a[1])  // valid index
	fmt.Println(a[10]) // invalid index (too large)
}
```

``` text
./array.go:8:16: invalid argument: index -1 (constant of type int) must not be negative
./array.go:10:16: invalid argument: index 10 out of bounds [0:5]
```
But when we wrap the access in a function, Go no longer statically detects the out of bounds index.

``` go
package main
import "fmt"
func main() {
	a := [5]int{2, 3, 5, 7, 11}
	getItem(a, -1)
	getItem(a, 1)
	getItem(a, 10)
}
func getItem(a [5]int, i int) {
	fmt.Println(a[i])
	// panic: runtime error: index out of range [-1]
}
```
If we run the program, we get a **runtime error**:
``` sh
panic: runtime error: index out of range [-1]

goroutine 1 [running]:
main.getItem(...)
        /home/gobra/array.go:20
```
Note that Go is memory safe and checks if the index is in range
as opposed to C [^1] where out-of-bounds accesses are *Undefined Behavior*.


Now if we check the program with Gobra we can find the error statically at **verification time**.
``` go
Error at: </home/gobra/array.go:18:2> Assignment might fail. 
Index i into a[i] might be negative.
```

The indexing operation `v := a[i]` implicitly has the precondition
`requires 0 <= i && i < len(a)`
and postcondition
`ensures v == a[i]`

Unfortunately, we can not chain the comparisons and `0 <= i < len(a)` is not a valid Gobra assertion.

<!-- this is also checked in specs (e.g. not well defined) -->

Let us try to write an assertion that states than an array is sorted.
As a first attempt we might write
`requires arr[0] <= arr[1] <= arr[2] <= ... <= arr[N-1]`
Of course, we do not want to write specifications like this since this does not scale and would not work for if we have different lengths `N`.
Quantifiers allow us to be more precise.

## Quantifiers
Another way of specifying that an array is sorted,
is that for any two elements of the array,
the first element must be less than or equal to the second element.

### Universal quantifier `forall`
In Gobra, *for any* is realized by the `forall` quantifier.
We cannot directly pick any two elements,
but we can state that for any indices `i` and `j` of type `int`, `arr[i] <= arr[j]` as
`requires forall i, j int :: arr[i] <= arr[j]`
Note that we can quantify `i` and `j` at the same time, 
 instead of the more cumbersome
`requires forall i int :: forall j int :: arr[i] <= arr[j]`

Array indices must also be in bounds for specifications.
We need to constrain that `i` and `j` are valid indices, otherwise we see errors like:
``` text
Method contract is not well-formed. 
Index i into arr[i] might be negative.
```

### Implication `==>`
In Gobra the operator for the implication  *if P then Q* is `==>`.
This gives our final version for the precondition

```gobra
requires forall i, j int :: 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
func search(arr [N]int)
```

<!-- conceptual:
the assertion `forall i int :: P` is true
iff P is true when all free occurrences of i can be substituted with arbitrary values of type int (or T in general)
Note that this is very powerful:
For example for `forall i int64 :: P`
P has to hold for all of the \\(2^64\\) possible values for i
Testing all of those values is already infeasible.
 -->
<!--
In general, the syntax (could have different types?)
`forall IDENTIFIER [,IDENTIFIER]* T :: ASSERTION` -->
<!-- the forall assertion is true if T holds for all possible values -->
<!-- can we shadow identifiers? -->

<!-- make it clear it is powerful and makes it hard for the verifier -->
### Existential Quantifier `exists`
The other quantifier is `exists` and uses the same syntax.
As the name suggests, `exists` requires the assertion to be true for *at least one* value.

For example, we could state `arr` contains the value `0` as
``` gobra
exists i int :: 0 <= i && i < len(arr) ==> arr[i] == 0
```

`exists` should be used sparingly.
It can be a heavy burden for the verifier to find a witness among many possible values.
We show later how we can often use `ghost` code instead.


[^1]: 
Before accessing the element, the index is compared (`CMPQ`) to the length of the array (`$5`).
``` assembly
CMPQ    AX, $5
JCC     main_getItem_pc92
```
(compiled with x86-64 gcc 1.22.1)

``` c
#include <stdio.h>
int main(int argc, char *argv[]) {
    int a[] = {2, 3, 5, 7, 11};
    printf("%d, %d, %d\n", a[-1], a[1], a[10]);
    return 0;
}
```

``` sh
1, 3, 517856616 
```
Note that the `1` is not from the array `a` but in this case actually the `argc` that is stored on the stack before the array.


<!-- [^1]: The truth table of `P==>Q`. -->
<!-- | P ==> Q | Q=false | Q=true | -->
<!-- |:-------:|:-------:|:------:| -->
<!-- | P=false | 1       | 1      | -->
<!-- | P=true  | 0       | 1      | -->
