# Array Operations
<!--
explain preconditions of an indexing operation, make it clear that accesses out of bounds are excluded statically -->

In this section, we operate with arrays of fixed size `N`.
Note that an array is a value and therefore copied when passed to a function.
Later we will also look at slices.

Go can find out-of-bounds indices for constant values when compiling a program.
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
But when we wrap the access in a function, Go no longer statically detects the out-of-bounds index.

```go
package main
import "fmt"
func main() {
	a := [5]int{2, 3, 5, 7, 11}
	getItem(a, -1)
	getItem(a, 1)
	getItem(a, 10)
}
func getItem(a [5]int, i int) {
	fmt.Println(a[i]) // error
}
```
If we run the program, we get a _runtime error_:
``` sh
panic: runtime error: index out of range [-1]

goroutine 1 [running]:
main.getItem(...)
        /home/gobra/array.go:20
```
Note that Go is memory-safe and checks if the index is in range.
Now if we check the program with Gobra we can find the error statically at _verification time_.
``` go
ERROR Assignment might fail. 
Index i into a[i] might be negative.
```

The indexing operation `v := a[i]` implicitly has the precondition
`requires 0 <= i && i < len(a)`
and postcondition
`ensures v == a[i]`
Unfortunately, we can not chain the comparisons and `0 <= i < len(a)` is not a valid Gobra assertion.

<!-- this is also checked in specs (e.g. not well defined) -->


