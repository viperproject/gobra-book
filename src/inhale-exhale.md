# Inhaling and exhaling

Permissions can be manually added by inhaling and removed by exhaling.
This can be useful for debugging but should not be needed for normal verification purposes.

The statement `exhale ASSERTION`
1. asserts that all value constraints in `ASSERTION` hold
2. asserts that all permissions mentioned by `ASSERTION` are held
3. removes all permissions mentioned by `ASSERTION`

Exhale is similar to `assert`, with the difference that `assert` does not remove any permissions:
``` gobra
requires acc(x, 1)
func breatheOut(x *int) {
	assert acc(x, 1)
	exhale acc(x, 1/4)
	assert acc(x, 3/4)
	assert acc(x, 3/4) // no permission removed
}
```

The statement `inhale ASSERTION`
1. adds all permissions mentioned by `ASSERTION`
2. assumes all value constraints in `ASSERTION` hold

Inhale is similar to `assume`, with the difference that `assume` does not add any permissions:

``` gobra
requires acc(x, 1/2)
func breatheIn(x *int) {
	assume acc(x, 1/2)
	assert acc(x, 1/2)

	inhale acc(x, 1/2)
	assert acc(x, 1/1)
}
```
Assuming permission is held in a state where it is not yields a contradiction:
``` gobra
func contradiction(x *int) {
	// acc(x, 0)
	assume acc(x, 1/2)
	assert false
}
```

## References
[Viper Tutorial](https://viper.ethz.ch/tutorial/#inhale-and-exhale)
