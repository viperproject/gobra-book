# Mathematical types (`seq, set, mset, dict`)
This section gives an overview of the mathematical types supported by Gobra and their operations.
Examples illustrate the syntax and the operations.

Note that mathematical types are ghost types and may only be used in ghost code.

## Sequences (`seq`)
The type `seq[T]` represents a finite sequence with elements of type `T`.

| expression `E` | type of `x` | type of `y` | result type of `E` | description                                                                             |
|----------------|-------------|-------------|--------------------|--------------------------------------------------------------------------------------------|
| `x ++ y`       | `seq[T]`    | `seq[T]`    | `seq[T]`           | concatenation                                                                            |
| `x == y`       | `seq[T]`    | `seq[T]`    | `bool`             | equality                                                                                   |
| `x in y`       | `T`         | `seq[T]`    | `bool`             | `true` if and only if `x` is an element of `y`                                              |
| `seq[T]{}`     |             |             | `seq[T]`           | empty sequence                                                                    |
| `seq[T]{x, y}` | `T`         | `T`         | `seq[T]`           | literal[^1]                                                                     |
| `seq[x..y]`    | `I`       | `I`       | `seq[I]` [^2]        | integer sequence \\( [i, i+1, \ldots, j-1] \\)                                             |
| `len(x)`       | `seq[T]`    |             | `int`              | length                                                                                     |
| `x[i]`         | `seq[T]`    |             | `T`                | lookup element at index `i` [^3]                                        |
| `x[i = y]`     | `seq[T]`    | `T`         | `seq[T]`           | creates a sequence with element `y` at index `i`, otherwise identical to `x`. [^3] |
| `x[i:j]`       | `seq[T]`    |             | `seq[T]`           | sub-sequence [^4] |
| `seq(x)`       | `seq[T]`    |             | `seq[T]`           | conversion from a sequence                                                                 |
| `seq(x)`       | `seq[T]`    |             | `[N]T`             | conversion from an array of length `N`                                                     |

[^1]: Sequence literals can be constructed with an arbitrary number of elements. The table only contains an example for two elements.
[^2]: `I` is an arbitrary [integer type](https://go.dev/ref/spec#Numeric_types) (`byte`, `uint8`, `int`, ...)
[^3]: The indices `i` and `j` are of _integer_ type. Requires `0 <= i && i < len(x)`.
[^4]: Sub-sequence with elements between index `i` (inclusive) and index `j` (exclusive). If `i < 0` or `i` is omitted, the lower index is treated as 0. If `j > len(x)` or `j` is omitted, the upper index is treated as `len(x)`.

<!-- | `x[i:j]`       | `seq[T]`    |             | `seq[T]`           | sub-sequence \\( [x[i], x[i + 1], \ldots, x[j-1]] \\) | -->
<!-- | `x[:j]`       | `seq[T]`    |             | `seq[T]`           | sub-sequence \\( [x[0], x[1], \ldots, x[j-1]] \\) | -->
<!-- | `x[i:]`       | `seq[T]`    |             | `seq[T]`           | sub-sequence \\( [x[i], x[i + 1], \ldots, x[j-1]] \\) | -->
<!-- | `x[:]`       | `seq[T]`    |             | `seq[T]`           | sub-sequence \\( [x[0],x[1], \ldots, x[len(x)-1] \\) | -->


### Example: `seq[int]`
``` go
{{#include mathematical-types.gobra:seq}}
```

<!-- [gobra-libs for sequences](https://github.com/viperproject/gobra-libs/blob/main/seqs/seqs.gobra) -->

## Sets (`set`)
The type `set[T]` represents [mathematical sets](https://en.wikipedia.org/wiki/Set_(mathematics)) with elements of type `T`.

| expression `E`     | type of `x` | type of `y` | result type of `E` | description                            |
|--------------------|-------------|-------------|--------------------|------------------------------------------------|
| `set[T]{}`         |             |             | `set[T]`           | \\( \varnothing \\)                            |
| `set[T]{x, y}`     | `T`         | `T`         | `set[T]`           | \\( \\{x, y \\} \\), in general with an arbitrary number of elements.                            |
| `x union y`        | `set[T]`    | `set[T]`    | `set[T]`           | \\( x \cup y \\)                               |
| `x intersection y` | `set[T]`    | `set[T]`    | `set[T]`           | \\( x \cap y \\)                               |
| `x setminus y`     | `set[T]`    | `set[T]`    | `set[T]`           | \\( x \setminus y\\)                           |
| `x subset y`       | `set[T]`    | `set[T]`    | `bool`             | \\( x \subseteq y\\)                           |
| `x == y`       | `set[T]`    | `set[T]`    | `bool`             | \\( x = y\\)                           |
| `x in y`           | `T`         | `set[T]`    | `bool`             | \\( x \in y\\)                                 |
| `len(x)`           | `set[T]`    |             | `int`              | \\( \|x\| \\)                                  |
| `x # y`            | `T`         | `set[T]`    | int                | 1 if \\(x \in y\\) else 0                      |
| `set(x)`           | `set[T]`    |             | `set[T]`           | conversion from a set                          |
| `set(x)`           | `seq[T]`    |             | `set[T]`           | conversion from a sequence                     |
<!-- | `set(x)`           | `option[T]`    |             | `set[T]`           | conversion from an option                          | -->

 <!-- \\( \\cases{1  & \\text{if }x \\in y \\\\ 0 & \\text{else}} \\) -->


### Example: `set[int]`

``` go
{{#include mathematical-types.gobra:set}}
```

<!-- [gobra-libs for sets](https://github.com/viperproject/gobra-libs/blob/main/sets/sets.gobra) -->


## Multisets (`mset`)
The type `mset[T]` represents [multisets](https://en.wikipedia.org/wiki/Multiset) with elements of type `T`.
Multisets are like sets but may contain the same element multiple times.
The multiset operations respect the multiplicities of the elements.

| expression `E`     | type of `x` | type of `y` | result type of `E` | description                            |
|--------------------|-------------|-------------|--------------------|------------------------------------------------|
| `mset[T]{}`         |             |             | `mset[T]`           |
| `mset[T]{x, x}`     | `T`         | `T`         | `mset[T]`           | \\( \\{x, x \\} \\), in general with an arbitrary number of elements.                            |
| `x union y`        | `mset[T]`    | `mset[T]`    | `mset[T]`           | 
| `x intersection y` | `mset[T]`    | `mset[T]`    | `mset[T]`           |
| `x setminus y`     | `mset[T]`    | `mset[T]`    | `mset[T]`           |
| `x subset y`       | `mset[T]`    | `mset[T]`    | `bool`             |
| `x == y`       | `mset[T]`    | `mset[T]`    | `bool`             | 
| `x in y`           | `T`         | `mset[T]`    | `bool`             | 
| `len(x)`           | `mset[T]`    |             | `int`              |
| `x # y`            | `T`         | `mset[T]`   | int                | multiplicity of the element `x` in `y` |
| `mset(x)`           | `mset[T]`    |             | `mset[T]`           | conversion from a multiset                          |
| `mset(x)`           | `seq[T]`    |             | `mset[T]`           | conversion from a sequence                          |
<!-- | `mset(x)`           | `option[T]`    |             | `mset[T]`           | conversion from an option                          | -->

### Example: `mset[int]`
``` go
{{#include mathematical-types.gobra:mset}}
```


## Dictionaries (`dict`)
The type `dict[K]V` represents dictionaries with keys of type `K` and values of type `V`.

| expression `E` | type of `x` | type of `y` | result type of `E` | description                                                     |
|----------------|-------------|-------------|--------------------|-----------------------------------------------------------------|
| `dict[K]V{}`   |             |             | `dict[K]V`         | empty dict                                                      |
| `dict[K]V{x: y}`   |   `K`          |     `V`        | `dict[K]V`         | dict literal [^5] |
| `x == y`       | `dict[K]V`  | `dict[K]V`  | `bool`             | equality                                                        |
| `x[y]`         | `dict[K]V`  | `K`         | `V`                | lookup the value associated with key `y` [^6]                                                    |
| `m[x = y]`     | `K`         | `V`         | `dict[K]V`         | dict with additional mapping `(x, y)`, otherwise identical to the dict `m` |
| `len(x)`       | `dict[K]V`  |             | int                | number of keys                                                 |
| `domain(x)`    | `dict[K]V`  |             | `set[K]`           | set of keys                                                     |
| `range(x)`     | `dict[K]V`  |             | `set[V]`           | set of values                                                   |

[^5]: In general, more items may be given. For duplicate keys, an error is reported:
    ``` go
    m1 := dict[string]int{ "one": 1, "two": 2, "one": -1}
    ```
    ``` text
    ERROR key appears twice in map literal
        m1 := dict[string]int{ "one": 1, "two": 2, "one": -1}
        ^
    ```
[^6]: Requires `y in domain(x)`. Otherwise, an error is reported:
    ``` go
    m1 := dict[string]int{ "one": 1, "two": 2}
    assert m1["three"] == 3
    ```
    ``` text
    ERROR Assert might fail. 
    Key "three" might not be contained in m1.
    ```
### Example: `dict[string]int`
``` go
{{#include mathematical-types.gobra:dict}}
```

<!-- [gobra-libs for dicts](https://github.com/viperproject/gobra-libs/blob/main/dicts/dicts.gobra) -->
