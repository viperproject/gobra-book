package sharedstruct

// ANCHOR: Scale
type Coord struct {
	x, y int
}

// @ requires acc(&c.x) && acc(&c.y)
// @ ensures acc(&c.x) && acc(&c.y)
// @ ensures c.x == old(c.x) * factor
// @ ensures c.y == old(c.y) * factor
func (c *Coord) Scale(factor int) {
	c.x = c.x * factor
	c.y = c.y * factor
}

// ANCHOR_END: Scale

// ANCHOR: client1
func client1() {
	c /*@@@*/ := Coord{1, 2} // changed
	c.Scale(5)
	// @ assert c == Coord{5, 10}
}

// ANCHOR_END: client1

// ANCHOR: client2
func client2() {
	c := &Coord{1, 2}
	c.Scale(5)
	// @ assert *c == Coord{5, 10}
}

// ANCHOR_END: client2

// ANCHOR: client3
func client3(c1, c2 Coord) {
	// @ share c1, c2  // <--- added
	c1.Scale(5)
	c2.Scale(-1)
}

// ANCHOR_END: client3
