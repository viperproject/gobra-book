// ANCHOR: all
package main

// ANCHOR: import
import "sync"

// ANCHOR_END: import
// ANCHOR: SafeCounter
// SafeCounter is safe to use concurrently.
type SafeCounter struct {
	mu    sync.Mutex
	count int
}

/*@
pred mutexInvariant(v *int) {
	acc(v)
}

pred (c *SafeCounter) Mem() {
	acc(c.mu.LockP()) && c.mu.LockInv() == mutexInvariant!<&c.count!>
}
@*/
// ANCHOR_END: SafeCounter

// ANCHOR: Increment
// @ requires acc(c.Mem(), _)
func (c *SafeCounter) Increment() {
	// @ unfold acc(c.Mem(), _)
	c.mu.Lock()
	// @ unfold mutexInvariant!<&c.count!>()
	c.count += 1
	// @ fold mutexInvariant!<&c.count!>()
	// @ c.mu.Unlock()
}

// ANCHOR_END: Increment

// ANCHOR: New
// @ ensures s.Mem()
func New() (s *SafeCounter) {
	c /*@@@*/ := SafeCounter{}
	// @ fold mutexInvariant!<&c.count!>()
	// @ (c.mu).SetInv(mutexInvariant!<&c.count!>)
	// @ fold c.Mem()
	return &c
}

// ANCHOR_END: New
// ANCHOR: main
func main() {
	ctr := New()
	go ctr.Increment()
	go ctr.Increment()
}

// ANCHOR_END: main

// ANCHOR_END: all

// ANCHOR: client
func client() {
	ctr := New()
	go ctr.Get()
	go ctr.Get()
	go ctr.Increment()
	go ctr.Increment()
}

// ANCHOR_END: client
// ANCHOR: Get
// @ requires acc(c.Mem(), 1/4)
// @ ensures acc(c.Mem(), 1/4)
func (c *SafeCounter) Get() int {
	// @ unfold acc(c.Mem(), 1/4)
	// @ defer fold acc(c.Mem(), 1/4) // <-----
	c.mu.Lock()
	defer c.mu.Unlock() // <-----
	// @ unfold mutexInvariant!<&c.count!>()
	// @ defer fold mutexInvariant!<&c.count!>() // <-----
	return c.count
}

// ANCHOR_END: Get

// ANCHOR: WG
// func client2() {
// 	ctr := New()
// 	var wg /*@@@*/ sync.WaitGroup
// 	for i := 0; i < 1000; i++ {
// 		wg.Add(1)
// 		// easier without closure?
// 		go func() {
// 			defer wg.Done()
// 			ctr.Increment()
// 		}()
// 	}
// 	wg.Wait()
// 	// counter.Get()
// }
// ANCHOR_END: WG
