# Abstracting memory with predicate interface members

In Gobra we can include predicate signatures within an interface.
This feature is particularly significant for abstracting memory, as interfaces define methods rather than fields, so we cannot specify access to concrete fields.
Each implementation must define its own predicate to abstract memory access.
Consequently, an interface can specify required behaviors without imposing constraints on the underlying data representation.

As an example, we consider the `Image` interface from the Go standard library.
It includes methods to retrieve the color `Model` (which itself is an interface) as well as a method to obtain a valid `Color` (also an interface) for a given pixel at coordinates (x, y).

The predicate `Mem` represents memory access and the ghost and pure function `Inv` represents an invariant that holds for the data structure storing the image.
``` go
{{#include ./image.go:Image}}
{{#include ./image.go:Geometry}}
```
<!-- make it pure to use in specs for At -->
Additionally, the boundaries of an image are encapsulated within a `Rectangle` struct, retrievable with the `Bounds` method.
For points not contained in this rectangle, `At` must return zero color.
We define zero color in terms of the `RGBA` method, or more precisely the corresponding pure and ghost method `RGBASpec`.
Since pure methods must have exactly one parameter, we cannot return `r, g, b, a`.
Instead, we define the ghost type `rgba`.
So, `rgba{}` represents the zero color.
``` go
{{#include ./image.go:Color}}
```

The type `*Alpha16Image` implements the `Image` interface.
To implement the interface any predicates defined for the interface must be implemented.
Here, the `Mem` predicate's body contains access to all fields of the struct, especially the elements of the `Pix` slice holding the image's pixel values.
``` go
{{#include ./image.go:Alpha16Image}}
```
The pure and ghost function `Inv` represents an invariant that has to hold for the image.
This invariant states that the entire entire size of the pixel slice is given by the stride times the height of the image:
`p.Stride*(p.Rect.Max.Y-p.Rect.Min.Y) == len(p.Pix)`,
where the `stride` is the distance in bytes between vertically adjacent pixels.
Note that the factor `2` in `p.Stride == 2*(p.Rect.Max.X-p.Rect.Min.X)` is due to the fact that each pixel uses 2 elements of the `Pix` slice for storage.
Additionally, the elements of the pixel slice are of type `uint8`, so they have values in the range from `0` to `0xff`.
While this could be inferred from the type alone, we have to state this due to a current limitation in Gobra.

``` go
{{#include ./image.go:Alpha16ImageInv}}
```

Please note that the annotations of the implementation and the interface must match.
A method defined as `ghost` in the interface, must also be implemented as `ghost`.
The same applies to `pure` methods.
An error is reported, for example, when we leave out `pure` for `Inv`:
``` text
ERROR  *Alpha16Image does not implement the interface Image
	reason: For member Inv, the 'pure' annotation for implementation and interface does not match
(*Alpha16Image) implements Image
^
```

The remaining methods:
- `ColorModel` is trivially implemented.
- For `Bounds`, we unfold the `Mem` predicate to obtain the concrete permission to read the field `p.Rect`.
- The method `At` is the trickiest to verify as we have to prove that the offset in the `Pix` array is within bounds, which we explain below.

``` go
{{#include ./image.go:Alpha16ImageMethods}}
```

Due to current limitations with bit operations, we replaced the bit-shift (`<<`) and bitwise OR (`|`) operations with arithmetic operations.
The original source used the following line.
``` go
c = Alpha16{uint16(p.Pix[i+0])<<8 | uint16(p.Pix[i+1])}
```
Note that the rewrite works because `p.Pix` has elements of type `uint8`.

We must show that `PixOffset` returns an offset satisfying `0 <= offset && offset < len(p.Pix) - 1`.
As `Point{x, y}` is contained in the rectangle `p.Rect`, `(y-p.Rect.Min.Y) >= 0` and `(x-p.Rect.Min.X) >= 0`.
Since stride is non-negative, `0 <= offset` immediately follows.

> TODO @João 
>   note about non-linear arithmetic

To prove `offset < len(p.Pix) - 1`, we help Gobra by providing proof annotations.
For the sake of explanation, we give verbose annotations.
Please note that they are not strictly necessary.
In the body of `PixOffset` above, a reduced proof is given.

We will need the assertions from `Inv`:
``` gobra
assert 2 * (p.Rect.Max.X - p.Rect.Min.X) == p.Stride && p.Stride * (p.Rect.Max.Y - p.Rect.Min.Y) == len(p.Pix)
```
First, we define a few ghost variables as abbreviations to simplify the offset calculation.
We can assert upper bounds on `dx` and `dy`, again since the point is contained in the rectangle.
``` gobra
offset = (y-p.Rect.Min.Y)*p.Stride + (x-p.Rect.Min.X)*2
ghost var height = p.Rect.Max.Y - p.Rect.Min.Y
ghost var dy = y-p.Rect.Min.Y
ghost var dx = (x-p.Rect.Min.X) * 2
assert offset == dy * p.Stride + dx
assert 0 <= dx && 0 <= dy && 0 <= offset
assert dy <= height - 1
assert dx <= p.Stride - 2
```
Next, we make use of the simple arithmetic fact that for \\(a, b, c \in \mathbb{N}\\) the following holds:
\\(a \leq b \implies a \cdot c \leq b \cdot c \\).
We define this lemma as a ghost function and invoke it with the appropriate arguments.
``` gobra
LemmaMulPos(y-p.Rect.Min.Y, p.Rect.Max.Y-p.Rect.Min.Y-1, p.Stride)
```
Afterwards, we can rewrite the inequality and arrive at the desired fact.
``` gobra
assert dy * p.Stride + dx <= (height - 1) * p.Stride + dx
assert offset <= (height - 1) * p.Stride + p.Stride - 2
assert offset <= len(p.Pix) - 2
```
The following example uses `*Alpha16Image` as an `Image`:
``` go
{{#include ./image.go:Alpha16Client}}
```

## Implementation without memory footprint
A `Rectangle` is also an `Image`, with bounds equal to the rectangle itself.
For points within the rectangle, `Opaque` color is returned and `Transparent` color otherwise.
No memory access is required in this case, and no invariant must be preserved.
The predicate `Mem` and the function `Inv` still have to be defined to implement `Image`.
We simply have `true` as the body and the return value respectively.
``` go
{{#include ./image.go:RectImpl}}
```

The full example with all image related interfaces can be found [here](./image.md).
