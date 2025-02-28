# Full example: `image`

``` go
{{#include ./image.go:all}}
```

TODO changes:
- Only a subset of the Go module
- Combined multiple packages into a single file
- Model not dynamically defined
- Renamed, e.g. `Alpha16Image` instead of `Alpha16` to not clash with the color `Alpha16`
- Small syntactical changes required by Gobra. E.g. fold statements before/after return
