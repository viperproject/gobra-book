# Goroutines and data races

This section covers goroutines, Go's lightweight threads, and how Gobra excludes _data races_, i.e., concurrent accesses to the same memory location with at least one modifying access.

For example, we use the type `Counter` with a method to `Increment` its count.

``` go
{{#include ./counter.go:Counter}}
{{#include ./counter.go:Increment}}
```

Goroutines run in the same address space, and concurrent calls to `Increment` cause data races for `c.count`.
For example, running the following snippet a few times, one may observe different values for `c.count` afterwards.
``` go
for i := 0; i < 1000; i++ {
	go ctr.Increment()
}
```

When a goroutine is dispatched with the `go` keyword, Gobra checks that the function or method's precondition holds.
We do not know the state of the goroutine after starting it; it may be in the middle of execution or may have already finished.
Hence, we do not get to assume the postcondition of the dispatched function or method.

``` go
{{#include ./counter.go:main}}
```
``` text
ERROR Precondition of call might not hold.

go ctr.Increment() might not satisfy the precondition of the callee.
```
In the above example, the permission `acc(&c.count)` is not transferred back after the first `go ctr.Increment()` statement.
But to start the second goroutine, `acc(&c.count)` is required.


With fractional permissions, we can split read permissions to multiple goroutines.
It is guaranteed that only one thread can have exclusive write permission to a memory location at a time.
Concurrent reads do not constitute a data race.

``` go
{{#include ./counter.go:Get}}
{{#include ./counter.go:client1}}
```

## Go's data race detector
Go has a built-in [data race detector](https://go.dev/doc/articles/race_detector), which can be enabled with the `-race` flag.
Note that only data races are found by dynamically running code.
Therefore, this detector is not guaranteed to find all data races. <!-- unsound -->

On the other hand, Gobra can statically prove the absence of data races in a program by reasoning with permissions.

In our example, a data race is detected.
``` text
> $ go run -race counter.go
==================
WARNING: DATA RACE
Read at 0x00c000012168 by goroutine 7:
  main.(*Counter).Increment()
      /home/gobra/counter.go:14 +0x35
  main.main.gowrap2()
      /home/gobra/counter.go:25 +0x17

Previous write at 0x00c000012168 by goroutine 6:
  main.(*Counter).Increment()
      /home/gobra/counter.go:14 +0x47
  main.main.gowrap1()
      /home/gobra/counter.go:24 +0x17

Goroutine 7 (running) created at:
  main.main()
      /home/gobra/counter.go:25 +0x104

Goroutine 6 (finished) created at:
  main.main()
      /home/gobra/counter.go:24 +0x94
==================
Found 1 data race(s)
exit status 66
```

