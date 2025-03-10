# Reasoning about mutual exclusion with `sync.Mutex`

- [ ] safeCounter version
  [goroutines example](./goroutine.md)

``` go
{{#include ./safeCounter.go:import}}
{{#include ./safeCounter.go:SafeCounter}}
```

- mutexInvariant predicate, resources that are protected by the Mutex.
  In this case, the memory location where `count` is stored.

- `acc(c.mu.LockP())`
  having access to this predicate enables us to Lock
- `c.mu.LockInv() == mutexInvariant!<&c.count!>`
  comparing first-class predicate, the mutex is associated with the right invariant

- mention stubs
  - abstract functions: signature and contract, no body
  - where the functions can be found (link)
  [local](/home/ali/Code/gobra-related/gobra/src/main/resources/stubs/sync/mutex.gobra) 
  - or produced in the stubs folder in the current working directory by running Gobra with the `--debug` flag.

- [ ] explain `LockP`, `LockInv`, `SetInv`, ...
- when we construct a new counter
- first fold the mutexInvariant
  - (why parentheses needed in which places)
- can associate this invariant with `SetInv`
- finally, we can fold the Mem predicate
  - how we synchronize access, e.g. by using sync.Mutex is an implementation detail and not exposed to clients of the public API
``` go
{{#include ./safeCounter.go:New}}
```

``` gobra
{{#include ./mutex.gobra:SetInv}}
{{#include ./mutex.gobra:LockInv}}
```

``` go
{{#include ./safeCounter.go:Increment}}
```

- consider including Lock / Unlock specs
``` gobra
{{#include ./mutex.gobra:Lock}}
{{#include ./mutex.gobra:Unlock}}
```

require only `acc(c.Mem(), _)` such that caller retains `acc(c.Mem(), _)` and can dispatch the second goroutine.
The program verifies.
``` go
{{#include ./safeCounter.go:main}}
```


- double Lock


- (termination, Lock has no decreases)
  - no Unlock

## Full `sync.Mutex` stubs
``` gobra
{{#include ./mutex.gobra:all}}
```
