# Maps

Go provides the built-in map data structure implementing a hash table.
``` go
watched := make(map[string]bool, 10) // optional capacity
//@ assert acc(watched) && len(watched) == 0
```
Permission is obtained from `make`.
The accessibility predicate `acc(watched)` is for the entire map.
Individual elements like in slices are not addressable.

Holding write permissions, we can add entries.
In specifications, we can check with `in` if a key is contained in the map.
``` go
watched["Blade Runner"] = true
//@ assert "Blade Runner" in watched && len(watched) == 1
```

The values can be retrieved with their keys.
``` go
elem, ok := watched["Blade Runner"]
//@ assert ok && elem
// non-existing key
elem, ok := watched["Dune"]
//@ assert !ok && !elem
```

Gobra does not support Go's built-in functions `delete` to remove map entries and `clear` to remove all map entries.


A `nil` map is obtained with `new` or by not initializing a map variable.
No elements can be added to a `nil` map.
Otherwise, it behaves like an empty map.
``` go
var rating map[string]int
//@ assert len(rating) == 0
r, ok := rating["Dune"]
//@ assert !ok && r == 0

rotten := new(map[string]int)
//@ assert len(*rotten) == 0
```

The key elements must be comparable.
For example one cannot use other maps, slices and functions as keys.

## Map Range
Range loops iterate over the keys and values for a map.
It is necessary to add a `with` clause (e.g. `range m /*@ with visited @*/`).
The ghost variable `visited` is a mathematical set (properly introduced in the next chapter) and contains the keys that have been visited already.

``` go
type Movie struct {
	name   string
	rating int
}

// @ requires acc(m, 1/2)
// @ requires len(m) > 0
func avgRating(m map[int]Movie) int {
	sum := 0
	//@ invariant acc(m, 1/2)
	//@ invariant len(m) > 0
	for _, movie := range m /*@ with visited @*/ {
		sum += movie.rating
	}
	return sum / len(m)
}

func critique() {
	nolan := map[int]Movie{
		// short: Movie may be ommitted
		132: {"Oppenheimer", 8},
		234: {"Tenet", 7},
		432: {"Dunkirk", 8},
	}
	//@ assert acc(nolan) && len(nolan) == 3
	avgRating(nolan)
}
```


Go does not specify the iteration order over maps [^1].
An entry added during iteration may be produced or skipped.
Gobra does not allow the mutation of maps while iterating.
``` go
// @ requires acc(m)
func produceSequels(m map[int]Movie) {
	//@ invariant acc(m)
	for id, movie := range m /*@ with visited @*/ {
		m[100*id] = Movie{movie.name + "2", movie.rating - 2} // error
	}
}

func main() {
	movies := map[int]Movie{
		132: {"Jaws", 6},
		234: {"Cars", 5},
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
map[132:{Jaws 6} 234:{Cars 5} 13200:{Jaws2 4} 23400:{Cars2 3} 1320000:{Jaws22 2} 2340000:{Cars22 1} 132000000:{Jaws222 0} 234000000:{Cars222 -1}]
```
``` text
map[132:{Jaws 6} 234:{Cars 5} 13200:{Jaws2 4} 23400:{Cars2 3} 2340000:{Cars22 1} 234000000:{Cars222 -1} 23400000000:{Cars2222 -3} 2340000000000:{Cars22222 -5} 234000000000000:{Cars222222 -7} 23400000000000000:{Cars2222222 -9}]
```

This is implemented by exhaling a small constant permission amount before the loop.
As a consequence, wildcard permission does not suffice:

``` go
// @ requires acc(m, _)
// @ requires len(m) > 0
func wildRating(m map[int]Movie) int {
	sum := 0
	//@ invariant acc(m, _)
	//@ invariant len(m) > 0
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

[^1]: [https://go.dev/ref/spec#For_range](https://go.dev/ref/spec#For_range) 
