// ANCHOR: all
package main

// ANCHOR: Color
// Color can convert itself to alpha-premultiplied 16-bits per channel RGBA.
// The conversion may be lossy.
type Color interface {
	// Returns true if the implementation holds a valid color.
	// @ ghost
	// @ pure
	// @ decreases
	// @ Valid() bool

	// RGBA returns the alpha-premultiplied red, green, blue and alpha values
	// for the color. Each value ranges within [0, 0xffff], but is represented
	// by a uint32 so that multiplying by a blend factor up to 0xffff will not
	// overflow.
	//
	// An alpha-premultiplied color component c has been scaled by alpha (a),
	// so has valid values 0 <= c <= a.
	// @ preserves Valid()
	// @ ensures 0 <= r && r <= a && 0 <= g && g <= a && 0 <= b && b <= a && a <= 0xffff
	RGBA() (r, g, b, a uint32)
}

// source: https://cs.opensource.google/go/go/+/refs/tags/go1.24.0:src/image/color/color.go;l=10
// ANCHOR_END: Color

// ANCHOR: Alpha16
// Alpha16 represents a 16-bit alpha color.
type Alpha16 struct {
	A uint16
}

// @ preserves c.Valid()
// @ ensures 0 <= r && r <= a && 0 <= g && g <= a && 0 <= b && b <= a && a <= 0xffff
func (c Alpha16) RGBA() (r, g, b, a uint32) {
	a = uint32(c.A)
	return a, a, a, a
}

// ANCHOR_END: Alpha16

// ANCHOR: Alpha16Valid
/*@
ghost
decreases
pure func (c Alpha16) Valid() bool {
	return 0 <= c.A && c.A <= 0xffff
}
@*/
// ANCHOR_END: Alpha16Valid

// ANCHOR: client1
func client1Alpha() {
	var c Color
	c = Alpha16{0xffff}
	r, _, _, a := c.RGBA()
	// @ assert 0 <= a && r <= a
}

// ANCHOR_END: client1

// ANCHOR: Constant
type Constant struct{}

// @ ensures r == 0x0 && g == 0xffff && b == 0xffff && a == 0xffff
func (c Constant) RGBA() (r, g, b, a uint32) {
	return 0x0, 0xffff, 0xffff, 0xffff
}

/*@
ghost
decreases
pure func (c Constant) Valid() bool {
	return true
}
@*/

func client1Constant() {
	var c Color
	c = Constant{}
	r, _, _, a := c.RGBA()
	// @ assert 0 <= a && r <= a
}

// ANCHOR_END: Constant

// ANCHOR: fail1
type Fail1 struct {
	p *uint32
}

// @ requires acc(c.p)
// @ requires c.Valid()
// @ ensures r <= 0xffff && g <= 0xffff && b <= 0xffff && a <= 0xffff
func (c Fail1) RGBA() (r, g, b, a uint32) {
	a = *c.p
	return a, a, a, a
}

/*@
ghost
requires acc(c.p)
decreases
pure func (c Fail1) Valid() bool {
	return 0 <= *c.p && *c.p <= 0xffff
}
@*/

// ANCHOR: client2
func client2(c Color) {
	c = Fail1{new(uint32)}
	r, _, _, a := c.RGBA()
	// @ assert 0 <= a && r <= a
}

// ANCHOR_END: client2
// ANCHOR_END: fail1

// ANCHOR: fail2
type Fail2 struct{}

// @ ensures 0 <= r && r <= a && 0 <= g && g <= a && 0 <= b && b <= a
// @ ensures c.Valid()
func (c Fail2) RGBA() (r, g, b, a uint32) {
	return 255, 255, 255, 255
}

/*@
ghost
decreases
pure func (c Fail2) Valid() bool {
	return true
}
@*/

func client3() {
	var c Color
	c = Fail2{}
}

// ANCHOR_END: fail2
// ANCHOR_END: all
