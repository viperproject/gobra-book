# Full example: `image`

``` go
{{#include ./image.go:all}}
```

- Only a subset of the [Go image package](https://pkg.go.dev/image) 
- Combined multiple packages into a single file
  - Renamed, e.g., `Alpha16Image` instead of `Alpha16` to not clash with the color `Alpha16`
- Small syntactic changes. 
  - For example, to insert `fold` statements before/after `return`
  - Color models not dynamically defined
