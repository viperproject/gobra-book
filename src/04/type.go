// ANCHOR: all
package main

// ANCHOR: Color
// without specifications for simplicity
type Color interface {
	RGBA() (r, g, b, a uint32)
}

// ANCHOR_END: Color

// ANCHOR: ColorImpl
type Alpha16 struct {
	A uint16
}

type Constant struct{}

// @ ensures r == 0x0 && g == 0xffff && b == 0xffff && a == 0xffff
func (c Constant) RGBA() (r, g, b, a uint32) {
	return 0x0, 0xffff, 0xffff, 0xffff
}

func (c Alpha16) RGBA() (r, g, b, a uint32) {
	a = uint32(c.A)
	return a, a, a, a
}

// ANCHOR_END: ColorImpl

// ANCHOR: Model
// Model can convert any [Color] to one from its own color model. The conversion
// may be lossy.
type Model interface {
	// @ requires c != nil
	// @ ensures res != nil
	Convert(c Color) (res Color)
}

// ANCHOR_END: Model

// ANCHOR: ConvertClient
func converting() {
	c1 := Constant{}
	c2 := Alpha16Model.Convert(c1)
	c3 := c2.(Alpha16)
	c3.RGBA()
}

// ANCHOR_END: ConvertClient

// ANCHOR: alpha16Model
type alpha16Model struct{}

var Alpha16Model alpha16Model

// @ requires c != nil
// @ ensures res != nil
// @ ensures typeOf(res) == type[Alpha16]
func (_ alpha16Model) Convert(c Color) (res Color) {
	if _, ok := c.(Alpha16); ok {
		return c
	}
	_, _, _, a := c.RGBA()
	return Alpha16{uint16(a)}
}

// ANCHOR_END: alpha16Model
// @ alpha16Model implements Model

// ANCHOR_END: all
// ANCHOR: TypeAssertionFail
// @ requires c != nil
func TypeAssertion(c Color) {
	c1 := c.(Alpha16) // error
	r, g, b, a := c1.RGBA()
	// @ assert r == g
}

// ANCHOR_END: TypeAssertionFail
