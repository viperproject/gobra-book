package main

// ANCHOR: readArrFinal
// @ requires 0 <= i && i < len(a)
// ANCHOR: readArr
func readArr(a [5]int, i int) int {
	b := a[i]
	return b
}

// ANCHOR_END: readArr
// ANCHOR_END: readArrFinal

// ANCHOR: client
func client1() int {
	a := [5]int{2, 3, 5, 7, 11}
	b1 := a[-1] // invalid index (too small)
	b2 := a[1]  // valid index
	b3 := a[10] // invalid index (too large)
	return b1 + b2 + b3
}

// ANCHOR_END: client

// ANCHOR: main
func main() {
	a := [5]int{2, 3, 5, 7, 11}
	readArr(a, -1)
	readArr(a, 1)
	readArr(a, 10)
}

// ANCHOR_END: main
