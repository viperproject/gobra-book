# `unfolding` predicates

The `unfolding P in E` statement temporarily unfolds the predicate instance `P` in a pure expression `E` and folds it back.

For example, the `pure` function `Head` uses `unfolding` in its body to temporarily get permissions for `l.Value`:
``` go
{{#include listMem.go:head}}
```
Due to the syntactic restrictions of `pure` functions, there is no other way of using the `fold` and `unfold` statements.

Recall that the predicate instance `l.Mem()` is transferred back implicitly for the `pure` function.

<!-- ``` go -->
<!-- 	ll = New(11, Empty()) -->
<!-- 	// @ assert ll.Mem() -->
<!-- 	// @ assert ll.Head() == 11 -->
<!-- 	// @ assert ll.Mem() -->
<!-- ``` -->

