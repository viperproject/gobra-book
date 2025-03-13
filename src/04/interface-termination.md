# Interfaces and termination

<div class="warning">
Termination checking for interfaces is currently buggy.

- TODO [issue #865](https://github.com/viperproject/gobra/issues/865) 
- TODO [issue #864](https://github.com/viperproject/gobra/issues/865) 
</div>

If an interface method specifies termination,
any implementation method must be proven to terminate.
Termination measures must be comparable between the interface and its implementation.
For example, if the interface uses a constant termination measure, the implementation must not use a predicate termination measure.

The termination measure of the implementation must be _stronger_ than the termination measure of the interface.

If the constant termination measure is `decreases 5`, an implementation must use a smaller constant, e.g., `decreases 3`.


An error is reported if we try to implement [sort.Interface](./sort.md), where the implementing `Swap` method has no termination measure:
``` text
ERROR Generated implementation proof (IntSlice implements interface{ View, Len, LessSpec, Less, LessIsConnected, LessIsTransitive, Swap }) failed. Function might not terminate. 

Required termination condition might not hold.
```

It is admissible for an interface method to not specify termination, but implementation methods may optionally provide termination measures.


> If an interface method specifies a termination measure, the implementing method must have a termination measure that is at least as strong.
