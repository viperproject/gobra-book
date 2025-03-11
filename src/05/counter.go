// ANCHOR: all
package main

// ANCHOR: Counter
type Counter struct {
	count int
}

// ANCHOR_END: Counter

// ANCHOR: Increment
// @ requires acc(&c.count)
// @ ensures acc(&c.count)
func (c *Counter) Increment() {
	c.count += 1
}

// ANCHOR_END: Increment
// ANCHOR: Get
// @ requires acc(&c.count, 1/8)
func (c *Counter) Get() int {
	return c.count
}

// ANCHOR_END: Get

// ANCHOR: main
func main() {
	ctr := new(Counter)
	go ctr.Increment()
	go ctr.Increment() // error
}

// ANCHOR_END: main

// ANCHOR: client1
// @ requires acc(&ctr.count, 1/2)
func client1(ctr *Counter) {
	go ctr.Get()
	go ctr.Get()
	go ctr.Get()
	go ctr.Get()
}

// ANCHOR_END: client1

// ANCHOR_END: all
