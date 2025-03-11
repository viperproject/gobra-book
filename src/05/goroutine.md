# Goroutines

- introduce example
- define data race

``` go
{{#include ./counter.go:Counter}}
{{#include ./counter.go:Increment}}
```

- permissions not transferred back after `go ...`

``` go
{{#include ./counter.go:main}}
```

``` text
ERROR Precondition of call might not hold.

go ctr.Increment() might not satisfy the precondition of the callee.
```

- explain the error

<!--
// Printing `ctr.Get()`
``` go
for i := 0; i < 1000; i++ {
	go ctr.Increment()
}
```
``` text
> $ go run counter.go
978
```
-->

-  maybe show concurrent reads are ok


``` go
{{#include ./counter.go:Get}}
{{#include ./counter.go:client1}}
```

- mention `go run -race`
  - highlight difference to Gobra

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

