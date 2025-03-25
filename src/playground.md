# Playground
You can edit the code below.
Use the buttons to verify it with Gobra or run it as a Go program.
```go, editable
package main

// @ ensures found ==> 0 <= idx && idx < len(arr) && arr[idx] == target
// @ ensures !found ==> forall i int :: {arr[i]} 0 <= i && i < len(arr) ==> arr[i] != target
func LinearSearch(arr [10]int, target int) (idx int, found bool) {
	// @ invariant 0 <= i && i <= len(arr)
	// @ invariant forall j int :: 0 <= j && j < i ==> arr[j] != target
	for i := 0; i < len(arr); i += 1 {
		if arr[i] == target {
			return i, true
		}
	}
	return -1, false
}

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
