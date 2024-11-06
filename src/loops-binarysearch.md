# Binary Search

We will follow along the example of function `binarySearch(arr [N]int, value int) (idx int)` that efficiently finds the rightmost position `idx` in a sorted array of integers `arr` where `value` would be inserted according to the sorted order.
Our approach is to gradually add specifications and fix errors along the way.
If you want to see the final code only you can skip to the end of this chapter.

Let us begin by writing the specification.
First, we must require the `arr` to be sorted.
We have already seen how we can write this as a precondition:
``` gobra
requires forall i, j int :: 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j]
```

To understand the the behavior we want to achieve we can look at a small example.
Note that for values like `1` contained in `arr` we want the index just after the last occurrence of that value to be returned.
``` gobra
arr := [7]int{0, 1, 1, 2, 3, 5, 8}
binarySearch(arr, -1) == 0
binarySearch(arr, 0) == 1
binarySearch(arr, 1) == 3
binarySearch(arr, 8) == 7
binarySearch(arr, 9) == 7
```
<!-- we can't assert them with our version...  -->

All values to the left of `idx` should compare less or equal to `value`
and all values from `idx` to the end of the array should be strictly greater than `value`.
``` gobra
ensures forall i int :: 0 <= i && i < idx ==> arr[i] <= value
ensures forall j int :: idx <= j && j < len(arr) ==> value < arr[j]
```
Something is still missing.
An issue is that the `Index j into arr[j] might be negative` since we only have `idx <= j` and no lower bound for `idx`.
Similarly, the `Index i into arr[i] might exceed sequence length`.
After constraining `idx` to be between `0` and `N` we are ready to implement `binarySearch`:
``` gobra
// @ requires forall i, j int :: 0 <= i && i < j && j < N ==> arr[i] <= arr[j]
// @ ensures 0 <= idx && idx <= N
// @ ensures forall i int :: 0 <= i && i < idx ==> arr[i] <= value
// @ ensures forall j int :: idx <= j && j < len(arr) ==> value < arr[j]
func binarySearch(arr [N]int, value int) (idx int) {
	low := 0
	high := N
	mid := 0
	for low < high {
		mid = (low + high) / 2
		if arr[mid] <= value {
			low = mid + 1
		} else {
			high = mid
		}
	}
	return low
}
```
We will have to add several invariants until we can verify the function.

First Gobra complains that the `Index mid into arr[mid] might be negative.`

So our first invariant is, that `mid` remains a valid index for `arr`:
``` go
	// @ invariant 0 <= mid && mid < N
```
Let's check manually if this invariant works.
1. Before the first iteration `mid` is initialized to `N / 2` hence `0 <= N / 2 && N / 2 < N` trivially holds.
2. For an arbitrary iteration, we assume that before this iteration `0 <= mid && mid < N` was true. Now we need to show that after updating `mid = (low + high) / 2`  the invariant is still true (the rest of the body does not influence mid). But we fail to do so as the invariant does not capture the values `low` and `high`.

So let us add what we know about `low` and `high` to help the verifier.
``` go
	// @ invariant 0 <= low && low < high && high < N
	// @ invariant 0 <= mid && mid < N
```
With this change we fixed the *Index-Error* but are confronted with a new error.
``` text
Loop invariant might not be preserved. 
Assertion low < high might not hold.
```
While `low < high` is true before the first iteration (assuming `N>0`)
and holds by the loop condition at the beginning of every except the last iteration.
But an invariant must hold after every iteration, including the last.
This is achieved by changing `low < high` to `low <= high`.

Note that after exiting the loop we know `!(low < high)` because the loop condition must have failed and `low <= high` from the invariant.
Together this implies `low == high`.

Our next challenge is:
``` text
Postcondition might not hold. 
Assertion forall i int :: 0 <= i && i < idx ==> arr[i] <= value might not hold.
```

So we need to find assertions that describe which parts of the array we have already searched.
The goal is that after the last iteration the invariants together with `low == high` should be able prove the postconditions.

For this step it is useful to think about how binary search works.
The slice `arr[low:high]` denotes the part of the array we still have to search for and which is halved every iteration.
In the prefix `arr[:low]` are no elements larger than `value`
and in the suffix `arr[high:]` no elements smaller or equal than `value`.
Exemplified for `binarySearch([7]int{0, 1, 1, 2, 3, 5, 8}, 4)`:

| `low` | `mid` | `high` | `arr[low:]`   | `arr[high:]` |
|-------|-------|--------|---------------|--------------|
| 0     | 0     | 7      | []            | []           |
| 4     | 3     | 7      | [0 1 1 2]     | []           |
| 6     | 5     | 7      | [0 1 1 2 3 5] | []           |
| 6     | 6     | 6      | [0 1 1 2 3 5] | [8]          |

Translating the above into Gobra invariants gives:
``` go
// @ invariant forall i int :: 0 <= i && i < low ==> arr[i] <= value
// @ invariant forall j int :: high <= j && j < N ==> value < arr[j]
```

When the function returns, `idx == low` holds and as discussed above also `low == high`.
We can clearly see that `low` and `high` with `idx` yields the postconditions:

``` go
// @ ensures forall i int :: 0 <= i && i < idx ==> arr[i] <= value
// @ ensures forall j int :: idx <= j && j < len(arr) ==> value < arr[j]
```

Now we can be happy because `Gobra found no errors`.

We will see `binarySearch` search again when we look at termination and do overflow checking.

## Full Example

``` go
// @ requires forall i, j int :: 0 <= i && i < j && j < N ==> arr[i] <= arr[j]
// @ ensures 0 <= idx  && idx <= N
// @ ensures forall i int :: 0 <= i && i < idx ==> arr[i] <= value
// @ ensures forall j int :: idx <= j && j < len(arr) ==> value < arr[j]
func binarySearch(arr [N]int, value int) (idx int) {
	low := 0
	high := N
	mid := 0
	// @ invariant 0 <= low && low <= high && high <= N
	// @ invariant forall i int :: 0 <= i && i < low ==> arr[i] <= value
	// @ invariant forall j int :: high <= j && j < N ==> value < arr[j]
	// @ invariant 0 <= mid && mid < N
	for low < high {
		mid = (low + high) / 2
		if arr[mid] <= value {
			low = mid + 1
		} else {
			high = mid
		}
	}
	return low
}
```

<!-- Client Code  -->
<!-- ``` go -->
<!-- // @ requires forall i, j int :: 0 <= i && i < j && j < len(arr) ==> arr[i] <= arr[j] -->
<!-- // @ ensures found == -1 ==> forall i int :: 0 <= i && i < len(arr) ==> arr[i] != value -->
<!-- // @ ensures found != -1 ==> 0 <= found && found < len(arr) && arr[found] == value -->
<!-- func find(arr [N]int, value int) (found int) { -->
<!-- 	idx := binarySearch(arr, value) -->
<!-- 	if idx == 0 || arr[idx-1] != value { -->
<!-- 		return -1 -->
<!-- 	} else { -->
<!-- 		return idx - 1 -->
<!-- 	} -->
<!-- } -->
<!-- ``` -->

