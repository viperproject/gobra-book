package main

const N = 10

// @ ensures forall i int :: 0 <= i && i < len(arr) ==> arr[i] <= res
// @ ensures 0 <= idx && idx < len(arr) && arr[idx] == res
func Max(arr [N]int) (res int /*@ , ghost idx int @*/) {
	res = arr[0]
	// @ invariant 0 <= i0 && i0 <= N
	// @ invariant forall j int :: 0 <= j && j < i0 ==> arr[j] <= res
	// @ invariant 0 <= idx && idx < N && arr[idx] == res
	for i, a := range arr /*@ with i0 @*/ {
		if a > res {
			res = a
			// @ ghost idx = i
		}
	}
	return res /*@ , idx @*/
}

func client() {
	arr := [10]int{0, 2, 4, 8, 10, 1, 3, 5, 7, 9}
	// @ assert arr[4] == 10
	// @ ghost var idx int
	m /*@, idx @*/ := Max(arr)
	// @ assert arr[idx] == m
	// @ assert m == 10
}
