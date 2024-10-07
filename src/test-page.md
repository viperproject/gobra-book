# Test Page

## Go block
```go,editable
package tutorial
func contains(s []int, x int) (isContained bool) {

  for i := 0; i < len(s); i += 1 {
    if s[i] == x {
      return true, i
    }
  }

  return false, 0
}
```

some inline code `v := <- ch`

```go,editable
package main
import "fmt"
func main() {
    fmt.Println("Hello world")
}
```

## Gobra Block
```gobra,editable
package tutorial

requires forall k int :: 0 <= k && k < len(s) ==> acc(&s[k], 1/2)
ensures  forall k int :: 0 <= k && k < len(s) ==> acc(&s[k], 1/2)
ensures  isContained ==> 0 <= idx && idx < len(s) && s[idx] == x
func contains(s []int, x int) (isContained bool, ghost idx int) {

  invariant 0 <= i && i <= len(s)
  invariant forall k int :: 0 <= k && k < len(s) ==> acc(&s[k], 1/4)
  for i := 0; i < len(s); i += 1 {
    if s[i] == x {
      return true, i
    }
  }

  return false, 0
}
```
## Highlight JS
```go
package tutorial

func contains(s []int, x int) (isContained bool, idx int) {

  for i := 0; i < len(s); i += 1 {
    if s[i] == x {
      return true, i
    }
  }

  return false, 0
}
```
## Mathjax

\\[\frac{\left(\mathbf{\{P\}}^{\prime}\right) s \left(\mathbf{\{Q\}}^{\prime}\right)}{\mathbf{\{P\}} s \mathbf{\{Q\}}} \left(\operatorname{Cons}\right) \quad \text{if } \mathbf{\{P\}} \vDash \mathbf{\{P\}}^{\prime} \text{ and } \mathbf{\{Q\}}^{\prime} \vDash \mathbf{\{Q\}}\\]

## Hiding lines
This block is not highlighted since highlight.js does not know gobra.
```gobra,should_panic
~package tutorial

requires forall k int :: 0 <= k && k < len(s) ==> acc(&s[k], 1/2)
ensures  forall k int :: 0 <= k && k < len(s) ==> acc(&s[k], 1/2)
ensures  isContained ==> 0 <= idx && idx < len(s) && s[idx] == x
func contains(s []int, x int) (isContained bool, ghost idx int) {

  invariant 0 <= i && i <= len(s)
  invariant forall k int :: 0 <= k && k < len(s) ==> acc(&s[k], 1/4)
  for i := 0; i < len(s); i += 1 {
    ~if s[i] == x {
    ~  return true, i
    ~}
  }

  return false, 0
}
```


```go,editable,mdbook-runnable,should_panic,compile_fail,runnable
package tutorial
func contains(s []int, x int) (isContained bool) {

  for i := 0; i < len(s); i += 1 {
    if s[i] == x {
      return true, i
    }
  }

  return false, 0
}
```
## Quizzes

And now, a _quiz_:

{{#quiz ../quizzes/rust-variables.toml}}
