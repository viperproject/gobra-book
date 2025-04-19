# Inhaling and exhaling

Permissions can be added to the verification state by inhaling and removed by exhaling.
This can be useful for debugging but should not be needed for normal verification purposes.

## Removing permissions with `exhale`
The statement `exhale ASSERTION`
1. checks that all value constraints in `ASSERTION` hold; otherwise, an error is reported.
2. checks that all permissions mentioned by `ASSERTION` are held; otherwise, an error is reported.
3. removes all permissions mentioned by `ASSERTION`

Exhale is similar to `assert`, with the difference that `assert` does not remove any permissions:
``` go does_not_verify
// @ requires acc(x, 1)
func breatheOut(x *int) {
	// @ assert acc(x, 1)
	// @ exhale acc(x, 1/4)
	// @ assert acc(x, 3/4)
	// @ assert acc(x, 3/4) // no permission removed
	// @ exhale acc(x, 1) // error
}
```
``` text
ERROR Exhale might fail. 
Permission to x might not suffice.
```
The last `exhale` failed because, at this point, only a permission amount of `3/4` is held.

## Adding permissions with `inhale`
The statement `inhale ASSERTION`
1. adds all permissions mentioned by `ASSERTION`
2. assumes all value constraints in `ASSERTION` hold

<div class="warning">
Inhaling can result in an inconsistent state.
Do not use it without a good reason, except for debugging and learning.
</div>

``` go verifies
// @ requires acc(x, 1/2)
func breatheIn(x *int) {
	// @ assert acc(x, 1/2)
	// @ inhale acc(x, 1/2)
	// @ assert acc(x, 1/1)
}
```

By inhaling a permission amount of 1 for the pointer `x` while already holding `acc(x, 1/2)`, we reach an inconsistent state, and `false` can be asserted:
``` go verifies
// @ requires acc(x, 1/2)
func breatheMore(x *int) {
	// @ inhale acc(x, 1)
	// @ assert acc(x, 3/2)
	// @ assert false
}
```

