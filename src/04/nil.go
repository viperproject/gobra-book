// ANCHOR: all
package main

// ANCHOR: fail1
// without specifications for simplicity
type Color interface {
	RGBA() (r, g, b, a uint32)
}

func main() {
	var c Color
	// @ assert c == nil
	client1(c)
}

func client1(c Color) {
	c.RGBA() // error
}

// ANCHOR_END: fail1

// ANCHOR: fail2
func client2() {
	var c Color = (*SomeColor)(nil)
	// @ assert c != nil
	// @ assert typeOf(c) == type[*SomeColor]
	c.RGBA()
}

type SomeColor struct{ x int }

func (s *SomeColor) RGBA() (r, g, b, a uint32) {
	// @ assert s != nil // error
	a = uint32(s.x)
	return a, a, a, a
}

// ANCHOR_END: fail2

// ANCHOR_END: all
