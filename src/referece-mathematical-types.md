# Mathematical types (`seq, set, mset, dict`)

Mathematical types are ghost types and can therefore only be used in ghost code.


## Sequences (`seq`)
The type `seq[T]` represents a [mathematical sequence](https://en.wikipedia.org/wiki/Sequence).

``` go
{{#include mathematical-types.gobra:seq}}
```


[gobra-libs for sequences](https://github.com/viperproject/gobra-libs/blob/main/seqs/seqs.gobra)

## Sets (`set`)
The type `set[T]` represents a [mathematical set](https://en.wikipedia.org/wiki/Set_(mathematics)).

``` go
{{#include mathematical-types.gobra:set}}
```

[gobra-libs for sets](https://github.com/viperproject/gobra-libs/blob/main/sets/sets.gobra)

## Multisets (`mset`)
The type `mset[T]` represents [multisets](https://en.wikipedia.org/wiki/Multiset).
Multisets are like sets, but may contain the same element multiple times.

``` go
{{#include mathematical-types.gobra:mset}}
```


## TODO Dictionaries (`dict`)

``` go
{{#include mathematical-types.gobra:dict}}
```

[gobra-libs for dicts](https://github.com/viperproject/gobra-libs/blob/main/dicts/dicts.gobra)
