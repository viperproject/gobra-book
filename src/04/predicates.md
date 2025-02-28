# Predicate interface members

In Gobra we can include predicate signatures within an interface.
This feature is particularly significant for abstracting memory, as interfaces define methods rather than fields, thereby we cannot specify access to concrete fields.
Using a predicate to abstract memory access, each implementation must define its own predicate.
Consequently, an interface can specify required behaviors without imposing constraints on the underlying data representation.

As an example we consider the `Image` interface from the Go standard library.
It includes methods to retrieve the color `Model`, which itself is an interface, as well as a method to obtain a `Color` (also an interface) for a given pixel at coordinates (x, y).
Additionally, the boundaries of an image are encapsulated within a `Rectangle` struct.
The predicate `Mem` represents memory access and the ghost and pure function `Inv` represents an invariant that holds for the data structure storing the image.
``` go
{{#include ./image.go:Image}}
{{#include ./image.go:Geometry}}
```

In this section we focus on abstracting memory and do not fully specify the image, for example we do not enforce that `Bounds` returns the domain for which `At` can return non-zero color.

The type `*Alpha16Image` implements the `Image` interface.
As for methods, to implement the interface any predicates defined for the interface must be implemented.
Here, the `Mem` predicate, whose body contains access to all fields of the struct, and especially the elements of the `Pix` slice holding the image's pixel values.
``` go
{{#include ./image.go:Alpha16Image}}
```
The pure and ghost function `Inv` represents an invariant that has to hold for the image.
Here it holds that the entire size of the pixel slice is given by the stride times the height of the image:
`p.Stride * (p.Rect.Max.Y - p.Rect.Min.Y) == len(p.Pix))`,
where the `stride` is the distance in bytes between vertically adjacent pixels.
Note that the factor `2` in `p.Stride == 2 * (p.Rect.Max.X - p.Rect.Min.X)` is due to the fact that each pixel uses 2 elements of the `Pix` slice for storage.

``` go
{{#include ./image.go:Alpha16ImageInv}}
```

Please note that annotations of the implementation and the interface must match.
A method defined as `ghost` in the interface, must also be implemented as `ghost`.
The same applies to `pure` methods.
An error is reported, for example when we leave out `pure` for `Inv`:
``` text
ERROR  *Alpha16Image does not implement the interface Image
	reason: For member Inv, the 'pure' annotation for implementation and interface does not match
(*Alpha16Image) implements Image
^
```

The remaining methods:
- `ColorModel` is trivially implemented
- For `Bounds` we unfold the `Mem` predicate to obtain the concrete permission to read the field `p.Rect`.
- The method `At` is the trickiest to verify as we have to prove that the offset in the `Pix` array is within bounds, which we explain below.

``` go
{{#include ./image.go:Alpha16ImageMethods}}
```

We must show that `PixOffset` returns an offset with `0 <= offset && offset < len(p.Pix) - 1`.
As `Point{x, y}` is contained in the rectangle `p.Rect`, `(y-p.Rect.Min.Y) >= 0` and `(x-p.Rect.Min.X) >= 0`.
Since stride is non-negative, `0 <= offset` immediately follows.

> TODO @João 
>   note about non-linear arithmetic

To prove `offset < len(p.Pix) - 1` we help Gobra by providing proof annotations.
We will need the assertions from `Inv`:
`2 * (p.Rect.Max.X - p.Rect.Min.X) == p.Stride && p.Stride * (p.Rect.Max.Y - p.Rect.Min.Y) == len(p.Pix)`.
First we define a few ghost variables as abbreviations, to simplify the offset calculation as `dy * p.Stride + dx`
We can assert upper bounds on `dx` and `dy`, again since the point is contained in the rectangle.
Next, we make use of the simple arithmetic fact that for \\(a, b, c \in \mathbb{N}\\) the following holds:
\\(a \leq b \implies a \cdot c \leq b \cdot c \\).
We define this Lemma as a ghost function and invoke it with the appropriate arguments.
Afterwards, we can rewrite the inequality and arrive at the desired fact.
Note that not all assert statements are necessary but we keep them for readability.


## Implementation without memory footprint
A `Rectangle` is also an `Image` whose bounds are the rectangle itself.
For points within the rectangle, `Opaque` color is returned and `Transparent` color otherwise.
No memory access is required in this case, and no invariant must be preserved.
The predicate `Mem` and the function `Inv` still have to be defined to implement `Image`.
We simply have `true` as the body and the return value respectively.
``` go
{{#include ./image.go:RectImpl}}
```



<!-- // @ ensures Point{x, y}.InSpec(r.Bounds()) ? c == Opaque : c == Transparent -->

## TODO Full section example
<!-- TODO copy pastable example of this section -->
