package purefuncs

// ANCHOR: cube
// @ pure
// @ decreases
func Cube(x int) int {
	return x * x * x
}

// @ requires n >= 0
func client(n int) {
	// @ assert 8 == Cube(2)
	// @ assert Cube(2) >= 8 && Cube(2) <= 8
	r := Cube(2)
	// @ assert Cube(n) >= 0
}

// ANCHOR_END: cube

// ANCHOR: fibonacci
/*@
ghost
requires n >= 0
decreases n
pure
func fibonacci(n int) (res int) {
    return n <= 1 ? n : fibonacci(n-1) + fibonacci(n-2)
}
@*/
// ANCHOR_END: fibonacci

// ANCHOR: client1
func client1(n int) {
	if n > 1 {
		// @ assert fibonacci(n) == fibonacci(n-1) + fibonacci(n-2)
	} else if n == 0 {
		// @ assert fibonacci(n) == 0
	}
}

// ANCHOR_END: client1

// ANCHOR: client2
func client2() {
	// @ assert fibonacci(3) == fibonacci(2) + fibonacci(1)
	// @ assert fibonacci(3) == 2
}

// ANCHOR_END: client2

// ANCHOR: client3
func client3() {
	// @ assert fibonacci(0) == 0
	// @ assert fibonacci(1) == 1
	// @ assert fibonacci(2) == 1
	// @ assert fibonacci(3) == 2
}

// ANCHOR_END: client3

// ANCHOR: fibIterative
// @ requires n >= 0
// @ ensures res == fibonacci(n)
func fibIterative(n int) (res int) {
	a, b := 0, 1
	// @ invariant 0 <= i && i <= n
	// @ invariant a == fibonacci(i)
	// @ invariant b == fibonacci(i+1)
	for i := 0; i < n; i++ {
		a, b = b, a+b
	}
	return a
}

// ANCHOR_END: fibIterative
