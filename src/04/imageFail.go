package image

// ANCHOR: ConvertFail
func client3() {
	var c Color
	// @ assert c == nil
	ConvertFail(c)
}

func ConvertFail(c Color) (res Color) {
	_, _, _, a := c.RGBA()
	return Alpha16{uint16(a)}
}

// ANCHOR_END: ConvertFail

// ANCHOR: ConvertFail2
func client4() {
	var c Color = (*Alpha16)(nil)
	// @ assert c != nil
	ConvertFail2(c)
}

// @ requires c != nil
func ConvertFail2(c Color) (res Color) {
	_, _, _, a := c.RGBA()
	// @ assert a >= 0
	return Alpha16{uint16(a)}
}

// ANCHOR_END: ConvertFail2

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
