# Verifying programs with arrays
<!--
explain preconditions of an indexing operation, make it clear that accesses out of bounds are excluded statically -->

In this section, we show how to verify programs that use arrays of fixed size
 (we will later see how to verify programs with slices, whose length may not be statically known).
Programs that access arrays often suffer from subtle bugs such as off-by-one errors, or other kinds of out-of-bounds accesses, that may lead to runtime panics.
Gobra prevents these by **statically** checking that every access to arrays is within bounds.

Go can find out-of-bounds indices for constant values when compiling a program.
``` go does_not_compile
{{#include ./array.go:client}}
```
``` text
./array.go:8:16: invalid argument: index -1 (constant of type int) must not be negative
./array.go:10:16: invalid argument: index 10 out of bounds [0:5]
```
Unfortunately, the checks that the Go compiler performs may miss simple out-of-bounds errors, as shown in the example below that moves the array access to a different function:

``` go panics
{{#include ./array.go:readArr}}
{{#include ./array.go:main}}
```
Go is memory-safe and checks at _runtime_ whether the index is within bounds:
``` sh
panic: runtime error: index out of range [-1]

goroutine 1 [running]:
main.readArr(...)
        /home/gobra/array.go:20
```
Now if we check the program with Gobra we can find the error statically at _verification time_.
``` text
ERROR Assignment might fail. 
Index i into a[i] might be negative.
```

<!-- and postcondition `ensures v == a[i]`. -->
The indexing operation `a[i]` implicitly has the precondition
`requires 0 <= i && i < len(a)`.
By propagating this precondition to the contract of `readArr`, Gobra accepts the function.
``` go verifies
{{#include ./array.go:readArrFinal}}
```
Then the calls `readArr(a, -1)` and `readArr(a, 10)` will get rejected.

> Gobra statically checks that every access to arrays is within bounds.

<!-- this is also checked in specs (e.g. not well defined) -->


