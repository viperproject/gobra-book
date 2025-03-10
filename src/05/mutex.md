# Reasoning about mutual exclusion with `sync.Mutex`

In this section, we study the lock [`Mutex`](https://pkg.go.dev/sync#Mutex) from Go's standard library, providing mutual exclusion.
As an example, we implement and specify `SafeCounter`, a variation of the `Counter` from the [goroutines example](./goroutine.md) that is safe to use concurrently.
Hence, at most one goroutine can modify the field `count` at a time.
``` go
{{#include ./safeCounter.go:import}}
{{#include ./safeCounter.go:SafeCounter}}
```

The `mutexInvariant` predicate defines resources that are protected by the `Mutex`.
In this case, it specifies the memory location where `count` is stored.

The `Mem` predicate for `*SafeCounter` does not directly contain access permissions, 
but access to the resource `c.mu.LockP()` that will allow us to `Lock` the lock.
Additionally, `c.mu.LockInv() == mutexInvariant!<&c.count!>` specifies which invariant is associated with the mutex.
<!-- first-class predicate comparison -->

When we import the `sync` package, the 
[predefined specs](https://github.com/viperproject/gobra/blob/master/src/main/resources/stubs/sync/) for this package are provided by Gobra.
All predefined specs included in Gobra can be found [here](https://github.com/viperproject/gobra/tree/master/src/main/resources/stubs).

<!-- Alternatively  you can produce the stubs folder in the current working directory by running Gobra with the `--debug` flag. -->
<!-- Note that stubs are included only for a subset of the Go standard library. -->
<!-- You may have to provide your own -->
<!-- with the option `-I` the provided stubs can be overridden -->



This declares, among others, the methods `LockInv`, `SetInv`, and the predicate `LockP` which are not part of the Go API.
``` gobra
{{#include ./mutex.gobra:Mutex}}

{{#include ./mutex.gobra:LockP}}

{{#include ./mutex.gobra:SetInv}}

{{#include ./mutex.gobra:LockInv}}
```
We call them _stubs_ as they are abstract and only the signature with a contract is given.
Since no bodies are provided, the contracts are assumed to hold.
In the case of `Mutex`, the specification models the mutual exclusion property.

The ghost method `SetInv` can be called to initialize a mutex.
Access to the mutex (`acc(m)`) is required and the mutex is zero-valued (`*m == Mutex{}`).
This access is lost, so we may not "tamper" the lock after initialization.
To associate the predicate `inv` with the lock, we need to give up access to `inv()`.
Afterwards, `LockInv` returns the predicate `inv` and we obtain access to the resource `m.LockP()`.
``` go
{{#include ./safeCounter.go:New}}
```
When constructing a new `SafeCounter`,
we first fold the first-class predicate `mutexInvariant<!&c.count!>` that denotes the resource protected by the lock.
Then, we associate this invariant with the mutex using `SetInv`.
Finally, we can fold the `Mem` predicate for the `SafeCounter`.

This way, clients again only require holding `s.Mem()` predicates and we can hide the implementation detail of how access is synchronized with a Mutex, enforcing the information hiding principle.

Before we can annotate the `Increment` method, consider the specifications of `Lock` and `Unlock`:
``` gobra
{{#include ./mutex.gobra:Lock}}

{{#include ./mutex.gobra:Unlock}}
```
To call either `Lock` or `Unlock`, `acc(m.LockP(), _)` is required and must have been obtained by `SetInv`.
Since the predicate `LockP` is abstract (it has no body), there is no way for a client to obtain an instance by folding.
We may only call `Unlock` after previously calling `Lock`.
This is modeled by the predicate instance `m.UnlockP()`, which is required to call `Unlock` and can only be obtained by calling `Lock`
``` go
{{#include ./safeCounter.go:Increment}}
```
From unfolding `acc(c.Mem(), _)`, we obtain `acc(m.LockP(), _)` and satisfy the precondition of `c.mu.Lock`.
In turn, we get access to the predicate instances `m.UnlockP()` and `m.LockInv()()`.
Also from `c.Mem()`, we get that `c.mu.LockInv() == mutexInvariant!<&c.count!>`.
So we can unfold again to get permissions to increment `c.count`.
To `Unlock` the mutex, the `mutexInvariant` must be folded back.


As `Increment` requires only `acc(c.Mem(), _)`, the caller retains `acc(c.Mem(), _)` and can dispatch the second goroutine.
The program verifies.
``` go
{{#include ./safeCounter.go:main}}
```


<!-- - TODO double Lock: quiz? -->
<!-- - TODO unlock without Lock: quiz? -->
<!-- - (TODO termination limitation, Lock has no decreases, may never call Unlock) -->

<!-- ## Full example -->
<!-- ``` go -->
<!-- {{#include ./safeCounter.go:all}} -->
<!-- ``` -->

## Full `sync.Mutex` stubs
``` gobra
{{#include ./mutex.gobra:all}}
```
