# Predicates and fractional permissions

Predicate instances are _resources_, i.e., permissions are used to track access to them.
So far, we have been using `l.Mem()`, a shorthand for specifying a permission amount of `1` to the predicate instance `l.Mem()`.
Equivalently, we can write `acc(l.Mem())` or `acc(l.Mem(), 1)` using the access predicate.


<!-- ``` go -->
<!-- {{#include list.go:mem}} -->
<!-- ``` -->

We may specify a permission amount' p` for `fold`, `unfold`, and `unfolding`.
In this case, any permission amount in the body of the predicate is multiplied by `p`.
For example, the body of `l.Mem()` contains `acc(l)` and `l.next.Mem()`.
After `unfold acc(l.Mem())`, only `acc(l, 1/2)` and `acc(l.next.Mem(), 1/2)` are held.

``` go verifies
{{#include list.go:fractional}}
```

`List` methods such as `Head` and `Get` do not need write permissions.
Hence, we change their contracts to only require `acc(l.Mem(), 1/2)`, and update any fold operations to use the correct permission amount.
We still require write access for methods like `Remove` that modify the `List`.
For now, disregard `l.View()` in the contracts.
``` go verifies
{{#include list.go:head}}
{{#include list.go:get}}
{{#include list.go:remove}}
```
Fractional permissions are crucial to frame properties.
When retaining a positive permission amount across a call of `Get`, we know the list is not modified.
If write permissions were required, the contract would need to state that the list does not get modified explicitly.


For pointers, `acc(x, 2)` implies `false`.
For predicates, we may have permission amounts larger than 1.
For example, we can have `acc(p2(l), 2)`, which denotes access to two predicate instances `p2(l)`.
``` go verifies
{{#include list.go:pred2}}
```
