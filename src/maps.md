# Maps

Go provides the built-in map data structure implementing a hash table.
``` go
watched := make(map[string]bool, 10) // optional capacity
// @ assert acc(watched) && len(watched) == 0
```
Permission to a map is obtained on allocation, e.g. from `make`.
The accessibility predicate `acc(watched)` is for the entire map.
Individual elements, as in slices, are not addressable.

Holding write permissions, we can add entries.
In specifications, we can check with `in` if a key is contained in the map.
``` go
watched["Blade Runner"] = true
// @ assert "Blade Runner" in watched && len(watched) == 1
```

The values can be retrieved with their keys.
Note that key elements must be comparable.
For example, one cannot use other maps, slices, and functions as keys.
``` go
elem, ok := watched["Blade Runner"]
// @ assert ok && elem
// non-existing key
elem, ok := watched["Dune"]
// @ assert !ok && !elem
```

## `nil` map
A `nil` map is obtained with `new` or by not initializing a map variable.
No permission is held for the `nil` map and no elements can be added.
Otherwise, it behaves like an empty map.
``` go
var rating map[string]int
// @ assert acc(rating, noPerm)
// @ assert len(rating) == 0
r, ok := rating["Dune"]
// @ assert !ok && r == 0

rotten := new(map[string]int)
// @ assert len(*rotten) == 0
```
We can read from the `nil` map as we would from an empty map, even without permission.
For functions that read from a map `m`,
the precondition `m != nil ==> acc(m, 1/2)` is typically used to support both `nil` and non-nil maps.

<!--
``` go
// @ requires m != nil ==> acc(m, 1/2)
func consume(m map[int]int)

func client() {
	var nilmap map[int]int
	consume(nilmap)
	nonnil := map[int]int{0: 1, 1: 1}
	consume(nonnil)
}
```
-->

## Range clause for maps
Range loops iterate over the keys and values for a map.
A `with` clause must be added (e.g. `range m /*@ with visited @*/`).
The ghost variable `visited` is a mathematical set (introduced in the next chapter) that contains the keys already visited.
In the following snippet, we build a map literal, with keys representing identifiers and `Movie` structs as values.
The function `avgRating` computes the average rating of all movies in a map.
We focus on the loop and omit the full functional specification for simplicity.

<!-- TODO change after https://github.com/viperproject/gobra/issues/808 -->

``` go
package movies

type Movie struct {
	name   string
	rating int
}

// @ requires acc(m, 1/2)
// @ requires len(m) > 0
func avgRating(m map[int]Movie) int {
	sum := 0
	// @ invariant acc(m, 1/2)
	// @ invariant len(m) > 0
	for _, movie := range m /*@ with visited @*/ {
		sum += movie.rating
	}
	return sum / len(m)
}

func critique() {
	nolan := map[int]Movie{
		132: {"Oppenheimer", 8},
		234: {"Tenet", 7},
		432: {"Dunkirk", 9},
	}
	// @ assert acc(nolan) && len(nolan) == 3
	avgRating(nolan) // 8
}
```

Go does not specify the iteration order over maps (see [^1]).
An entry added during iteration may either be produced or skipped.
Gobra prohibits the mutation of maps while iterating.
<!-- TODO connect/motivate -->
``` go
package main

type Movie struct {
	name   string
	rating int
}

// @ requires acc(m)
func produceSequels(m map[int]Movie) {
	// @ invariant acc(m)
	for id, movie := range m /*@ with visited @*/ {
		m[2*id] = Movie{movie.name + "2", movie.rating - 2} // error
	}
}

func main() {
	movies := map[int]Movie{
		2: {"Jaws", 6},
		3: {"Cars", 5},
	}
	produceSequels(movies)
	// fmt.Println(movies)
}
```
``` text
ERROR Assignment might fail. 
Permission to m might not suffice.
```
The output of the Go program is nondeterministic (two samples):
``` text
map[2:{Jaws 6} 3:{Cars 5} 4:{Jaws2 4} 6:{Cars2 3} 8:{Jaws22 2}]
```
``` text
map[2:{Jaws 6} 3:{Cars 5} 4:{Jaws2 4} 6:{Cars2 3} 12:{Cars22 1} 24:{Cars222 -1} 48:{Cars2222 -3} 96:{Cars22222 -5} 192:{Cars222222 -7} 384:{Cars2222222 -9}]

```

Mutation is prevented by exhaling a small constant permission amount to the map before the loop.
As a consequence, the wildcard permission amount is insufficient:
``` go
// @ requires acc(m, _)
// @ requires len(m) > 0
func wildRating(m map[int]Movie) int {
	sum := 0
	// @ invariant acc(m, _)
	// @ invariant len(m) > 0
	for _, movie := range m /*@ with visited @*/ {
		sum += movie.rating
	}
	return sum / len(m)
}
```
``` text
ERROR Range expression should be immutable inside the loop body.
Permission to m might not suffice.
```

## `delete` and `clear`
Gobra does not support Go's built-in function `delete` for removing map entries or `clear` for removing all map entries.


[^1]: [https://go.dev/ref/spec#For_range](https://go.dev/ref/spec#For_range) 
