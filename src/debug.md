# Debug

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

moooooore wyrd worz
```
##  math again
\\[ test \operatorname \\]

lkjdsaf \\( \frac{inline}{meths}\\)

## Hiding lines
ths grmmr is sooo wrong
This block is not highlighted since highlight.js does not know Gobra.
```go,hide-boring
~package tutorial

//@ requires forall k int :: 0 <= k && k < len(s) ==> acc(&s[k], 1/2)
//@ ensures  forall k int :: 0 <= k && k < len(s) ==> acc(&s[k], 1/2)
//@ ensures  isContained ==> 0 <= idx && idx < len(s) && s[idx] == x
func contains(s []int, x int) (isContained bool, ghost idx int) {

  //@ invariant 0 <= i && i <= len(s)
  //@ invariant forall k int :: 0 <= k && k < len(s) ==> acc(&s[k], 1/4)
  for i := 0; i < len(s); i += 1 {
    ~if s[i] == x {
    ~  return true, i
    ~}
  }

  return false, 0
}
```


```go,editable,runnable
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

## Warning

<div class="warning">
This is a bad thing that you should pay attention to.
Warning blocks should be used sparingly in documentation, to avoid "warning
fatigue," where people are trained to ignore them because they usually don't
matter for what they're doing.
</div>


<div class="hidden">This will not be seen.</div>

<img class="right" src="gobra.png" alt="The Rust logo">

## Timeout
```gobra,hide-boring
{{#include timeout.gobra}}
```
