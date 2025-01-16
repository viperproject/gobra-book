# Binary Search

We will follow along with the example of the function `BinarySearchArr(arr [N]int, target int) (idx int, found bool)`,
adapted from [Go's BinarySearch for slices](https://cs.opensource.google/go/go/+/refs/tags/go1.23.4:src/slices/sort.go;l=126).
Here we use arrays of integers instead of generic slices:
The contract we write formalizes the docstring:
``` go
// BinarySearch searches for target in a sorted slice and returns the earliest
// position where target is found, or the position where target would appear
// in the sort order; it also returns a bool saying whether the target is
// really found in the slice. The slice must be sorted in increasing order.
func BinarySearch[S ~[]E, E cmp.Ordered](x S, target E) (int, bool)
```

The following snippet shows the expected results for a test cases:
``` go
~func main() {
	arr := [7]int{0, 1, 1, 2, 3, 5, 8}
	fmt.Println(BinarySearchArr(arr, 2))   // 3 true
	fmt.Println(BinarySearchArr(arr, 4))   // 5 false
	fmt.Println(BinarySearchArr(arr, -1))  // 0 false
	fmt.Println(BinarySearchArr(arr, 10))  // 7 false
~}
```

Our approach is to gradually add specifications and fix errors along the way.
To see the final code only, you can skip to the end of this section.

Let us begin by writing a first contract.
First, we must require the array `arr` to be sorted.
We have already discussed how to specify this:
``` go
// @ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
```
If `BinarySearchArr` returns not found, `target` must not be an element of `arr`,
or equivalently, all elements of `arr` are not equal to `target`:
``` go
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
```
For the case where `target` is found, `idx` gives its position:
``` go
// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
```

This contract does not yet capture that `idx` must be the first index where `target` is found or otherwise the position where `target` would appear in the sort order.

Here is the first implementation of `BinarySearchArr`.
The elements with an index between `low` and `high` denote the parts of the array that remain to be searched for `target`.
We must add several loop invariants until this function satisfies its contract.
``` go
~const N = 1000
~
// @ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < N ==> arr[i] <= arr[j]
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
func BinarySearchArr(arr [N]int, target int) (idx int, found bool) {
	low := 0
	high := len(arr)
	mid := 0
	for low < high {
		mid = (low + high) / 2
		if arr[mid] < target {
			low = mid + 1
		} else {
			high = mid
		}
	}
	return low, low < len(arr) && arr[low] == target
}
```
``` text
ERROR Conditional statement might fail. 
Index mid into arr[mid] might be negative.
```

The variable `mid` is computed as the average of `low` and `high`.
After comparing `target` with the element `arr[mid]`, we can half the search range:
If target is larger, we search in the upper half between `mid+1` and `high`.
Otherwise, we search in the lower half between `low` and `mid`.
For this, we need the invariant that `mid` remains a valid index for `arr`:
``` go
	// @ invariant 0 <= mid && mid < len(arr)
```
Let us check whether this invariant works:
1. Before the first iteration `mid` is initialized to `0`. Therefore, `0 <= mid && mid < N` trivially holds.
2. For an arbitrary iteration, assume that the invariant `0 <= mid && mid < N` held before this iteration. Now we need to show that after updating `mid = (low + high) / 2`, the invariant is still holds (since the rest of the body does not influence `mid`).
However, this cannot be proven without establishing bounds for `low` and `high`.

We know that `low` and `high` stay between `0` and `len(arr)`,
and `low` should be smaller than `high`, right?
``` go
	// @ invariant 0 <= low && low < high && high <= len(arr)
	// @ invariant 0 <= mid && mid < len(arr)
```
``` text
ERROR Loop invariant might not be preserved. 
Assertion low < high might not hold.
```
The condition `low < high` holds before the first iteration and for every iteration except the last.
However, an invariant must hold after every iteration, including the last.
To address this, we weaken the condition `low < high` to `low <= high`.

Note that after exiting the loop, the loop condition gives `!(low < high)`, while the invariant ensures `low <= high`.
Together, these imply `low == high`.

Our next challenge is to find invariants that describe which parts of the array have already been searched and are guaranteed to not contain `target`.
By the final iteration, these invariants, combined with `low == high`, should be sufficient to prove the postcondition.
Currently we get the error:
``` text
ERROR Postcondition might not hold. 
Assertion !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target might not hold.
```

To help us find the invariant, let us exemplify the execution of binary search with concrete arguments `BinarySearchArr([7]int{0, 1, 1, 2, 3, 5, 8}, 4)`.
The following expressions are evaluated at the beginning of the loop and once after the loop:
| `low` | `high` | `arr[:low]` | `arr[low:high]` | `arr[high:]` |
|-------|--------|-------------|-------------------|----------------|
| 0     | 7      | []          | [0 1 1 2 3 5 8]   | []             |
| 4     | 7      | [0 1 1 2]   | [3 5 8]           | []             |
| 4     | 5      | [0 1 1 2]   | [3 5]             | [8]            |
| 5     | 5      | [0 1 1 2 3] | []               | [5 8]            |

We observe a pattern: the slice `arr[low:high]` denotes the part of the array we still have to search for.
All elements in the prefix `arr[:low]` are smaller than `target`, and all elements in the suffix `arr[high:]` are greater than or equal to `target`.
Translating this into invariants gives, we have:
``` go
	// @ invariant forall i int :: {arr[i]} 0 <= i && i < low ==> arr[i] < target
	// @ invariant forall j int :: {arr[j]} high <= j && j < len(arr) ==>  target <= arr[j]
```

Since the array is still known to be sorted, we can simplify this further by relating `target` to the elements
`arr[low-1]` and `arr[high]`, while ensuring that the indices remain within bounds.
``` go
	// @ invariant low > 0 ==> arr[low-1] < target
	// @ invariant high < len(arr) ==>  target <= arr[high]
```

When exiting the loop, we know that `low == high`.
If `target` is contained in `arr`, it must be located at index `low`, which we check for with `arr[low] == target`.
By combining all invariants, the postcondition can be proven now.
However, clients still fail to assert some desired properties.

``` go
func InitialClient() {
	arr := [7]int{0, 1, 1, 2, 3, 5, 8}
	i1, found1 := BinarySearchArr(arr, 1)
	i2, found2 := BinarySearchArr(arr, 2)
	i4, found4 := BinarySearchArr(arr, 4)
	// @ assert found1  // Assert might fail.
	// @ assert i1 == 1 // Assert might fail.
	// @ assert found2  // Assert might fail.
	// @ assert i4 == 5 // Assert might fail.
	// @ assert !found4
}
```
While we know for certain that 4 is not contained, the current postcondition does not provide any information about the index in other cases.
For example, it does not guarantee that the position of the first occurrence of duplicate 1s will be returned.
We need to include in the contract that `idx` is _the position where target would appear in the sort order_.
``` go
// @ ensures 0 <= idx && idx <= len(arr)
// @ ensures idx > 0 ==> arr[idx-1] < target
// @ ensures idx < len(arr) ==>  target <= arr[idx]
```
This stronger contract still follows from the loop invariants.
Let us take a step back and take a look at the contract which has grown quite large:
``` go
// @ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
// @ ensures 0 <= idx && idx <= len(arr)
// @ ensures idx > 0 ==> arr[idx-1] < target
// @ ensures idx < len(arr) ==> target <= arr[idx]
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
// @ ensures found ==> 0 <= idx < len(arr) && arr[idx] == target
func BinarySearchArr(arr [N]int, target int) (idx int, found bool)
```
We can simplify the cases with `!found` and `found` to
``` go
// @ found == (idx < len(arr) && arr[idx] == target)
```
The previous postcondition, `found ==> 0 <= idx < len(arr) && arr[idx] == target`, is directly covered by the new postcondition, combined with `0 <= idx && idx <= len(arr)`.
The other postcondition, `!found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target`, is also covered. For `!found`, one of the following must hold:

1. `idx >= len(arr)`. In this case, from `idx > 0 ==> arr[idx - 1] < target` and `idx <= len(arr)`, it follows that `arr[len(arr) - 1] < target`. This implies that `target` is not contained in the array, as the array is sorted.

2. `idx < len(arr)` and `arr[idx] != target`.
   From the postcondition `idx < len(arr) ==> target <= arr[idx]`, we can infer that `arr[idx] > target`. Since the array is sorted, `target` is not contained in `arr[idx:]`.
   Additionally, the postcondition `idx > 0 ==> arr[idx - 1] < target` ensures that `target` is not contained in `arr[:idx]`.


The full example can be found below.
<!-- We will see `BinarySearchArr` search again when we look at [termination](./termination.md) and [overflow checking](./overflow.md). -->

## Full Example

``` go
package binarysearcharr

const N = 7

func FinalClient() {
	arr := [7]int{0, 1, 1, 2, 3, 5, 8}
	i1, found1 := BinarySearchArr(arr, 1)
	// @ assert found1 && arr[i1] == 1 && i1 == 1
	i2, found2 := BinarySearchArr(arr, 2)
	// @ assert found2 && arr[i2] == 2 && i2 == 3
	i4, found4 := BinarySearchArr(arr, 4)
	// @ assert !found4 && i4 == 5
	i10, found10 := BinarySearchArr(arr, 10)
	// @ assert !found10 && i10 == len(arr)
}

// @ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
// @ ensures 0 <= idx && idx <= len(arr)
// @ ensures idx > 0 ==> arr[idx-1] < target
// @ ensures idx < len(arr) ==> target <= arr[idx]
// @ ensures found == (idx < len(arr) && arr[idx] == target)
func BinarySearchArr(arr [N]int, target int) (idx int, found bool) {
	low := 0
	high := len(arr)
	mid := 0
	// @ invariant 0 <= low && low <= high && high <= len(arr)
	// @ invariant 0 <= mid && mid < len(arr)
	// @ invariant low > 0 ==> arr[low-1] < target
	// @ invariant high < len(arr) ==> target <= arr[high]
	for low < high {
		// fmt.Println(low, high, arr[:low], arr[low:high], arr[high:])
		mid = (low + high) / 2
		if arr[mid] < target {
			low = mid + 1
		} else {
			high = mid
		}
	}
	// fmt.Println(low, high, arr[:low], arr[low:high], arr[high:])
	return low, low < len(arr) && arr[low] == target
}
```

