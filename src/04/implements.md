# Implementation proofs (`implements`)

In Gobra, a concrete type serving as the underlying type of an interface value must be a [behavioral subtype](./behavioral.md) of that interface.
An _implementation proof_ is needed when Gobra cannot prove this automatically.


For example, we consider the interface `Bounded` with a single method `Bounds` that returns a bounding rectangle.
Additionally, a `Mem` predicate is defined to abstract memory access.
``` go
{{#include ./implements.go:Bounded}}
```
We implement the `Bounded` interface for the type `(*Alpha16Image)`.
With the implementation of `Bounds` and the predicate `Mem`, 
`(*Alpha16Image)` fulfills all syntactic requirements for the `Bounded` interface.
``` go
{{#include ./implements.go:Alpha16ImageImpl}}
```
<!-- TODO: rename Alpha16Image to not confuse? Maybe simplify struct and Mem pred -->

The statement `T implements I` checks whether the type `T` is a behavioral subtype of the interface type `I`. Gobra tries an auto-generated proof, which may fail as seen in the following snippet:
``` go does_not_verify
// @ (*Alpha16Image) implements Bounded
```
``` text
ERROR Generated implementation proof (*Alpha16Image implements interface{ Bounds }) failed. Precondition of call to implementation method might not hold. 

Permission to p.Rect might not suffice.
```

The above failed since obtaining `acc(&p.Rect, 1/2)` from the interface's precondition `acc(Mem(), 1/2)` requires folding a predicate instance.
Gobra currently does not attempt to show this automatically.

We give an implementation proof following the `implements` keyword, 
where we must show that the implementation's precondition holds, given that the interface's precondition holds.
After calling the implementation method and establishing its postcondition, we must prove the postcondition of the interface method.
``` go verifies
{{#include ./implements.go:BoundsProof}}
```

For each method, we provide proof annotations in the body.
Currently, implementation proofs are subject to strict syntactic restrictions.
Besides calling the implementation method, we may only fold predicates and use `assert` statements.
Note that contracts are not repeated in the implementation proof.

In this case, after `unfold acc(p.Mem(), 1/2)`, the precondition of the implementation method holds, and we call `p.Bounds()`, then assign the out-parameter.
After `fold acc(p.Mem(), 1/2)`, the postcondition of the interface method holds.
Hence, the implementation proof succeeds.

## Predicates in implementation proofs
The implementations must declare predicates defined for an interface.
When the implementing type is not the predicate's receiver or the predicate's name differs,
the correct predicate must be assigned in the implementation proof.

In the above example, we declared the predicate `(p *Alpha16Image) Mem()`, which required no changes in the implementation proof.
Alternatively, consider if we defined the predicate `MyMem(p *Alpha16Image)`.
Then, we must add the highlighted line to the implementation proof:
``` go
/*@
pred MyMem(p *Alpha16Image) {
	acc(p) && forall i int :: {&p.Pix[i]} 0 <= i && i < len(p.Pix) ==> acc(&p.Pix[i])
}
@*/

/*@
(*Alpha16Image) implements Bounded {

	pred Mem := MyMem	// <--- assign the predicate

	(p *Alpha16Image) Bounds() (r Rectangle) {
		unfold acc(MyMem(p), 1/2) // instead of p.Mem()
		r = p.Bounds()
		fold acc(MyMem(p), 1/2)	  // instead of p.Mem()
		return
	}
}
@*/
```

### Implementation proof in different packages
An implementation proof may be placed in a different package from the implementation.
Similar to Go, where it is not possible to define new methods on a type from another package, we cannot define a predicate with a receiver from a different package.
For example, in the package `main`, we cannot declare the predicate `pred (x *image.Gray) Mem()`, so we must resort to something like `pred Mem(x *image.Gray)`.
Then, the predicate must be assigned in the implementation proof, as described above.

An example of this can be found [here](https://github.com/viperproject/gobra/tree/master/src/test/resources/regressions/examples/tutorial-examples/external-interface).

## Trivial implementation proofs

Alternatively, we can change the contract of `(p *Alpha16Image) Bounds()` to match the contract in the interface:
``` go
{{#include ./implements.go:ImageBounds}}
```
Then, we can omit the implementation proof and instead fold and unfold the `Mem` predicate.
In the other sections, most examples use this pattern.
``` go
// @ preserves acc(p.Mem(), 1/2)
func (p *Alpha16Image) Bounds() (r Rectangle) {
	// @ unfold acc(p.Mem(), 1/2)
	r = p.Rect
	// @ fold acc(p.Mem(), 1/2)
	return
}
```
  
<!-- > The statement `T implements I` checks whether the type `T` is a behavioral subtype of the interface type `I`. -->

## Full example
``` go verifies
{{#include ./implements.go:all}}
```
