# `defer` statements

A `defer` statement invokes a function whose execution is deferred to the moment the surrounding function returns ([spec](https://go.dev/ref/spec#Defer_statements)).
 
Defer statements are not directly related to concurrency, but we include them in this chapter because they frequently occur in concurrent code.
For example, a common pattern is to defer the call of the `Unlock` method for a mutex.
Here, we augment the [SafeCounter example](./mutex.md) with a method `Get`:
``` go
{{#include ./safeCounter.go:Get}}
{{#include ./safeCounter.go:client}}
```
We use `defer` three times, once deferring `c.mu.Unlock()` and in ghost code to defer folding the predicates `mutexInvariant` and `c.Mem`.

At the point of the `defer` statement, only the function and its parameters are evaluated, but the call is not yet evaluated.
Deferred functions or methods are executed in the reverse order they were deferred.
Gobra checks the contracts when they are executed.

For example, if we swap the order of the `defer` statements in the example above, Gobra reports an error
since when `Unlock` is executed, `mutexInvariant` has not been folded yet.
``` go
    // ...
	// @ defer fold mutexInvariant!<&c.count!>()
	defer c.mu.Unlock()
	return c.count
```
``` text
ERROR  Precondition of call might not hold. 
Permission to m.LockInv()() might not suffice.
```

<!-- maybe closures -->
