package image

// ANCHOR: TypeAssertionFail
// @ requires c != nil
func TypeAssertion(c Color) {
	c1 := c.(Alpha16)
	r, g, b, a := c1.RGBA()
	// @ assert r == g
}

// ANCHOR_END: TypeAssertionFail

// ANCHOR: ConvertClient
func converting() {
	c1 := Constant{}
	c2 := Alpha16Model.Convert(c1)
	c3 := c2.(Alpha16)
}

// ANCHOR_END: ConvertClient
