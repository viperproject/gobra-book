# Binary Search

We will follow along with the example of the function `BinarySearchArr(arr [N]int, value int) (found bool)` that efficiently searches a sorted array of integers and returns whether `value` is contained in the array.
The following snippet shows the expected results for a test array:
``` go
~func main() {
	arr := [7]int{0, 1, 1, 2, 3, 5, 8}
	fmt.Println(BinarySearchArr(arr, 2))   // true
	fmt.Println(BinarySearchArr(arr, 4))   // false
	fmt.Println(BinarySearchArr(arr, -1))  // false
	fmt.Println(BinarySearchArr(arr, 10))  // false
~}
```

Our approach is to gradually add specifications and fix errors along the way.
If you want to see the final code only you can skip to the end of this chapter.

Let us begin by writing the contract.
First, we must require the array `arr` to be sorted.
We have already seen how we can write this as a precondition:
``` go
//@ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
```
If `BinarySearchArr` returns not found, `value` must not be an element of `arr`,
or equivalently, all elements of `arr` are not equal to `value`:
``` go
//@ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != value
```
The full contract should include a case for when `value` is found.
While we could specify with an existential quantifier that there exists an index `idx` such that `arr[idx] == value`, this is not efficient and is discouraged.
Hence we omit this case and show later how a `ghost` parameter can be used instead.

Here is the first implementation of `BinarySearchArr` and its contract.
The elements with an index between `low` and `high` denote the parts of the array that remain to be searched for `value`.
We must add several loop invariants until this function satisfies its contract.
``` go
//@ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < N ==> arr[i] <= arr[j]
//@ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != value
func BinarySearchArr(arr [N]int, value int) (found bool) {
	low := 0
	high := len(arr) - 1
	mid := 0
	for low < high {
		mid = (low + high) / 2
		if arr[mid] == value {
			return true
		} else if arr[mid] < value {
			low = mid + 1
		} else {
			high = mid
		}
	}
	return arr[low] == value
}
```
``` text
ERROR Conditional statement might fail. 
Index mid into arr[mid] might be negative.
```

The variable `mid` is computed as the average of `low` and `high`.
If we compare `value` with the element `arr[mid]`, we either find it,
or we can half the search range:
We either continue searching in the lower half between `low` and `mid` or the upper half between `mid+1` and `high`.
For this, we need the invariant that `mid` remains a valid index for `arr`:
``` go
	//@ invariant 0 <= mid && mid < len(arr)
```
Let us check if this invariant works:
1. Before the first iteration `mid` is initialized to `0` hence `0 <= mid && mid < N` trivially holds.
2. For an arbitrary iteration, we assume that before this iteration `0 <= mid && mid < N` was true. Now we need to show that after updating `mid = (low + high) / 2`, the invariant is still true (the rest of the body does not influence mid). But this cannot be proven without bounds for `low` and `high`.

We know that `low` and `high` stay between `0` and `len(arr)`,
and `low` should be smaller than `high`, right?
``` go
	//@ invariant 0 <= low && low < high && high < len(arr)
	//@ invariant 0 <= mid && mid < len(arr)
```
``` text
ERROR Loop invariant might not be preserved. 
Assertion low < high might not hold.
```
With this change, we fix the _Index-Error_ but are confronted with a new error.
While `low < high` holds before the first iteration and holds for every iteration except the last.
But an invariant must hold after every iteration, including the last.
To account for this, we weaken `low < high` to `low <= high`.

Note that after exiting the loop we have `!(low < high)` from the loop condition and `low <= high` from the invariant.
Together this implies `low == high`.

``` text
ERROR Postcondition might not hold. 
Assertion !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != value might not hold.
```

Our next challenge is to find invariants that describe which parts of the array have been searched and do not contain `value`.
After the last iteration the invariants together with `low == high` should be enough to prove the postcondition.

Let us exemplify the execution of binary search with concrete arguments `BinarySearchArr([7]int{0, 1, 1, 2, 3, 5, 8}, 4)`.
The following expressions are evaluated at the beginning of the loop and once after the loop:
| `low` | `high` | `arr[:low]` | `arr[low:high+1]` | `arr[high+1:]` |
|-------|--------|-------------|-------------------|----------------|
| 0     | 6      | []          | [0 1 1 2 3 5 8]   | []             |
| 4     | 6      | [0 1 1 2]   | [3 5 8]           | []             |
| 4     | 5      | [0 1 1 2]   | [3 5]             | [8]            |
| 5     | 5      | [0 1 1 2 3] | [5]               | [8]            |

Here we can see the pattern that the slice `arr[low:high+1]` denotes the part of the array we still have to search for.
All elements in the prefix `arr[:low]` are smaller than `value` and all elements in the suffix `arr[high+1:]` are larger than `value`.
Translating the above into Gobra invariants gives:
``` go
//@ invariant forall i int :: {arr[i]} 0 <= i && i < low ==> arr[i] < value
//@ invariant forall i int :: {arr[i]} high < i && i < len(arr) ==>  value < arr[i]
```

When exiting the loop we either found `target` or know that 
all elements except at index `low` (which is equal to `high`) were not equal to `target`.
After the final test `arr[low] == value`, we know this for the entire array.
Combining all invariants the postcondition can be proven and `Gobra found no errors`.
We will see `BinarySearchArr` search again when we look at [termination](./termination.md) and [overflow checking](./overflow.md).

## Full Example

``` go
package binarysearcharr
const N = 7
//@ requires forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < N ==> arr[i] <= arr[j]
//@ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != value
func BinarySearchArr(arr [N]int, value int) (found bool) {
	low := 0
	high := len(arr) - 1
	mid := 0
	//@ invariant forall i, j int :: {arr[i], arr[j]} 0 <= i && i < j && j < N ==> arr[i] <= arr[j]
	//@ invariant 0 <= low && low <= high && high < len(arr)
	//@ invariant 0 <= mid && mid < len(arr)
	//@ invariant forall i int :: {arr[i]} 0 <= i && i < low ==> arr[i] < value
	//@ invariant forall i int :: {arr[i]} high < i && i < len(arr) ==>  value < arr[i]
	for low < high {
		mid = (low + high) / 2
		if arr[mid] == value {
			return true
		} else if arr[mid] < value {
			low = mid + 1
		} else {
			high = mid
		}
	}
	//@ assert low == high
	return arr[low] == value
}

func client() {
	arr := [7]int{0, 1, 1, 2, 3, 5, 8}
	//@ assert forall i, j int :: 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
	//@ assert arr[3] == 2	// trigger that 2 is contained
	found2 := BinarySearchArr(arr, 2)
	//@ assert found2
	found4 := BinarySearchArr(arr, 4)
	// we cannot assert !found4
}
```
