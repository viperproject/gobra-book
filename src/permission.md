# Permission

[//]: # ( introduce the example for this section )

```go
type Account struct {
	id      int
	balance int
}
```

[//]: # ( show how code fails that tries to read balance (maybe also modify))

```go
func calculate_interest(a *Account, amount int) float64 {
   return a.balance * 0.01
}
```

```go
//@ requires amount > 0
func topup(a *Account, amount int) {
   a.balance += amount 
}
```

if we have an instance `a` of type `Account`
`acc(&a.id) && acc(&a.balance)`

[//]: # ( what is the difference of acc(&a.id) and acc(a.id) ?)

We could write this in compact form
`acc(a)`


[//]: # ( acc(x)  in general )

[//]: # ( old(x) )

```go
//@ ensures old(a.balance) + amount == a.balance
func topup(a *Account, amount int) {
   a.balance += amount 
}
```

## Fractional Permission


[//]: # ( 1 for write "exclusive access")
[//]: # ( arbitrary positive to read )

[//]: # ( repeat if we have more than 1 this implies false)
[//]: # ( wildcard _ vs exists an amount (ensures we give back the same amount)  ; _ is not enough for writing)

[//]: # ( acc(x) )



[//]: # ( for pure functions (side effect free) returned implicitly)


## Abstracting access to unbounded Datastructures with predicates

```go
type Node struct {
	value int
	next  *Node
}
```

```gobra
pred llist(ptr *Node) {
  acc(&ptr.value) && acc(&ptr.next) && (ptr.next != nil ==> llist(ptr.next))
}
```
