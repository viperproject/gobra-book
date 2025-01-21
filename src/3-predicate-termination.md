# Predicates as termination measures

Predicate instances can be used as [termination](./termination.md) measures.
They decrease if an instance if nested within another predicate instance.
This measure is lower bounded since the predicate instance has a finite unfolding.

TODO: why we implement it recusively

``` go
{{#include list.go:length1}}
```

TODO

``` go
{{#include list.go:length}}
```


<!--
- iterative length / or getting last element
  - seen how to write a (recursive) function to get the length of a linked list
  - this function preserved access to the linked list
  - if we write an iterative version
  - traversing the list we must unfold access
  - it is not clear how we could fold it back to return back the full permission to the list
  - this can be achieved by using _magic wands_ , an advanced topic (link)
  - Example: iterative length without ensures Mem ... -->

<!-- TODO Technical footnote -->
