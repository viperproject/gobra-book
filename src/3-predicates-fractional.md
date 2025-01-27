# Predicates and fractional permissions

Predicate instances are _resources_, i.e., permissions are used to track access to them.
So far, we were using `l.Mem()`, which is a shorthand for specifying a permission amount of `1` to the predicate instance `l.Mem()`.
Equivalently we can write `acc(l.Mem())` or `acc(l.Mem(), 1)` using the access predicate.


<!-- ``` go -->
<!-- {{#include list.go:mem}} -->
<!-- ``` -->

For `fold`, `unfold`, and `unfolding` we may specify a permission amount `p`.
Then any permission amount in the body of the predicate is multiplied by `p`.
For example, the body of `l.Mem()` contains `acc(l)` and `l.next.Mem()`.
After `unfold acc(l.Mem())`, only `acc(l, 1/2)` and `acc(l.next.Mem(), 1/2)` is held.

``` go
{{#include list.go:fractional}}
```

`List` methods such as `Head` and `Get` do not need write permissions.
Hence we change their contracts to only require `acc(l.Mem(), 1/2)`, and update any fold operations to use the correct permission amount.
For methods like `Remove` that modify the `List`, we still require write access.
Please ignore `l.View()` in the contracts for now.
``` go
{{#include list.go:head}}
{{#include list.go:get}}
{{#include list.go:remove}}
```


<!-- TODO acc(P, 2) is not a contradiction (e.g. P could give 1/2 acc) -->
For pointers, `acc(x, 2)` implied `false`.
For predicates, we may have permission amounts larger than 1.
As an example, we can have `acc(p2(l), 2)`, which denotes access to two predicate instances `p2(l)`.
``` go
{{#include list.go:pred2}}
```
