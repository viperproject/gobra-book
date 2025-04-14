// ANCHOR: all
package image

// Copyright 2009 The Go Authors.

// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are
// met:

//    * Redistributions of source code must retain the above copyright
// notice, this list of conditions and the following disclaimer.
//    * Redistributions in binary form must reproduce the above
// copyright notice, this list of conditions and the following disclaimer
// in the documentation and/or other materials provided with the
// distribution.
//    * Neither the name of Google LLC nor the names of its
// contributors may be used to endorse or promote products derived from
// this software without specific prior written permission.

// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
// "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
// LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
// A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
// OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
// SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
// LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
// DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
// THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
// OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

// ANCHOR: Color
/*@
ghost type rgba ghost struct {
	r, g, b, a uint32
}

ghost
pure
decreases
func (c rgba) ColorRange() bool {
	return 0 <= c.r && c.r <= c.a && 0 <= c.g && c.g <= c.a &&
		0 <= c.b && c.b <= c.a && c.a <= 0xffff
}
@*/

// Color can convert itself to alpha-premultiplied 16-bits per channel RGBA.
// The conversion may be lossy.
type Color interface {
	// Returns true if the implementation holds a valid color.
	// @ ghost
	// @ pure
	// @ decreases
	// @ Valid() bool

	// @ ghost
	// @ requires Valid()
	// @ ensures c.ColorRange()
	// @ pure
	// @ decreases
	// @ RGBASpec() (ghost c rgba)

	// RGBA returns the alpha-premultiplied red, green, blue and alpha values
	// for the color. Each value ranges within [0, 0xffff], but is represented
	// by a uint32 so that multiplying by a blend factor up to 0xffff will not
	// overflow.
	//
	// An alpha-premultiplied color component c has been scaled by alpha (a),
	// so has valid values 0 <= c <= a.
	// @ preserves Valid()
	// @ ensures RGBASpec() == rgba{r, g, b, a}
	RGBA() (r, g, b, a uint32)
}

// ANCHOR_END: Color
// source: https://cs.opensource.google/go/go/+/refs/tags/go1.24.0:src/image/color/color.go;l=10

// ANCHOR: Alpha16
// Alpha16 represents a 16-bit alpha color.
type Alpha16 struct {
	A uint16
}

/*@
ghost
pure
requires c.Valid()
ensures res.ColorRange()
decreases
func (c Alpha16) RGBASpec() (res rgba) {
	return let a := uint32(c.A) in rgba{a, a, a, a}
}
@*/

/*@
ghost
decreases
pure func (c Alpha16) Valid() bool {
	return 0 <= c.A && c.A <= 0xffff
}
@*/

// @ preserves c.Valid()
// @ ensures c.RGBASpec() == rgba{r, g, b, a}
func (c Alpha16) RGBA() (r, g, b, a uint32) {
	a = uint32(c.A)
	return a, a, a, a
}

// ANCHOR_END: Alpha16

// ANCHOR: Model
// Model can convert any [Color] to one from its own color model. The conversion
// may be lossy.
type Model interface {
	// @ requires c != nil && c.Valid()
	// @ ensures res != nil && res.Valid()
	Convert(c Color) (res Color)
}

// ANCHOR_END: Model

// Go stdlib uses the following, which is not legal in Gobra.
// var Alpha16Model Model = ModelFunc(alpha16Model)

// ANCHOR: alpha16Model
type alpha16Model struct{}

var Alpha16Model alpha16Model

// @ requires c != nil && c.Valid()
// @ ensures res != nil && res.Valid()
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

// ANCHOR: Geometry
// A Point is an X, Y coordinate pair. The axes increase right and down.
type Point struct {
	X, Y int
}

// In reports whether p is in r.
// @ pure
// @ decreases
func (p Point) In(r Rectangle) (res bool) {
	return r.Min.X <= p.X && p.X < r.Max.X &&
		r.Min.Y <= p.Y && p.Y < r.Max.Y
}

// A Rectangle contains the points with Min.X <= X < Max.X, Min.Y <= Y < Max.Y.
// It is well-formed if Min.X <= Max.X and likewise for Y. Points are always
// well-formed. A rectangle's methods always return well-formed outputs for
// well-formed inputs.
//
// A Rectangle is also an [Image] whose bounds are the rectangle itself. At
// returns color.Opaque for points in the rectangle and color.Transparent
// otherwise.
type Rectangle struct {
	Min, Max Point
}

// ANCHOR_END: Geometry

// ANCHOR: Image
// Image is a finite rectangular grid of [Color] values taken from a color
// model.
type Image interface {
	// Mem represents the access to the memory of the Image
	// @ pred Mem()	// <----- Predicate member

	// Invariant that holds for valid images
	// @ ghost
	// @ pure
	// @ requires acc(Mem(), _)
	// @ decreases
	// @ Inv() bool

	// ColorModel returns the Image's color model.
	// @ ensures m != nil
	ColorModel() (m Model)

	// ANCHOR: ImageBounds
	// Bounds returns the domain for which At can return non-zero color.
	// The bounds do not necessarily contain the point (0, 0).
	// @ requires acc(Mem(), _)
	// @ pure
	// @ decreases
	Bounds() (r Rectangle)
	// ANCHOR_END: ImageBounds

	// At returns the color of the pixel at (x, y).
	// At(Bounds().Min.X, Bounds().Min.Y) returns the upper-left pixel of the grid.
	// At(Bounds().Max.X-1, Bounds().Max.Y-1) returns the lower-right one.
	// @ preserves acc(Mem(), 1/2)
	// @ preserves Inv()
	// @ ensures c != nil && c.Valid()
	// @ ensures !Point{x, y}.In(Bounds()) ==> (c.RGBASpec() == rgba{})
	At(x, y int) (c Color)
}

// ANCHOR_END: Image

// ANCHOR: RectImpl
/*@
// Mem implements the [Image] interface.
pred (r Rectangle) Mem() {
	true
}

// Inv implements the [Image] interface.
ghost
decreases
pure func (r Rectangle) Inv() bool {
	return true
}
@*/

// ColorModel implements the [Image] interface.
// @ ensures m != nil
func (r Rectangle) ColorModel() (m Model) {
	return Alpha16Model
}

// Bounds implements the [Image] interface.
// @ requires acc(r.Mem(), _)
// @ pure
// @ decreases
func (r Rectangle) Bounds() (res Rectangle) {
	return r
}

// At implements the [Image] interface.
// @ preserves acc(r.Mem(), 1/2)
// @ preserves r.Inv()
// @ ensures c != nil && c.Valid()
// @ ensures Point{x, y}.In(r.Bounds()) == (c.RGBASpec() != rgba{})
func (r Rectangle) At(x, y int) (c Color) {
	if (Point{x, y}).In(r) {
		return Alpha16{0xffff} // Opaque
	}
	return Alpha16{0} // Transparent
}

// @ Rectangle implements Image
// ANCHOR_END: RectImpl

var (
	Transparent = Alpha16{0}
	Opaque      = Alpha16{0xffff}
)

// cannot return them in (r Rectangle) At
// Valid might not be asserted for these global variables

// ANCHOR: Alpha16Image

// Alpha16Image is an in-memory image whose At method returns [color.Alpha16] values.
type Alpha16Image struct {
	// Pix holds the image's pixels, as alpha values in big-endian format. The pixel at
	// (x, y) starts at Pix[(y-Rect.Min.Y)*Stride + (x-Rect.Min.X)*2].
	Pix []uint8
	// Stride is the Pix stride (in bytes) between vertically adjacent pixels.
	Stride int
	// Rect is the image's bounds.
	Rect Rectangle
}

/*@
pred (p *Alpha16Image) Mem() {
	acc(p) && forall i int :: {&p.Pix[i]} 0 <= i && i < len(p.Pix) ==> acc(&p.Pix[i])
}
@*/

// ANCHOR_END: Alpha16Image

// ANCHOR: Alpha16ImageInv
/*@
ghost
requires acc(p.Mem(), _)
pure
decreases
func (p *Alpha16Image) Inv() bool {
	return unfolding acc(p.Mem(), _) in (2*(p.Rect.Max.X-p.Rect.Min.X) == p.Stride &&
    	p.Stride * (p.Rect.Max.Y-p.Rect.Min.Y) == len(p.Pix)) &&
    	forall i int :: {&p.Pix[i]} 0 <= i && i < len(p.Pix) ==> 0 <= p.Pix[i] && p.Pix[i] <= 0xff
}
@*/
// ANCHOR_END: Alpha16ImageInv

// ANCHOR: Alpha16ImageMethods

// @ ensures m != nil
func (p *Alpha16Image) ColorModel() (m Model) { return Alpha16Model }

// @ requires acc(p.Mem(), _)
// @ pure
// @ decreases
func (p *Alpha16Image) Bounds() (r Rectangle) {
	return /*@ unfolding acc(p.Mem(), _) in @*/ p.Rect
}

// @ requires acc(p.Mem(), 1/2)
// @ requires p.Inv()
// @ ensures acc(p.Mem(), 1/2)
// @ ensures p.Inv()
// @ ensures c != nil && c.Valid()
// @ ensures !Point{x, y}.In(p.Bounds()) ==> (c.RGBASpec() == rgba{})
func (p *Alpha16Image) At(x, y int) (c Color) {
	// @ unfold acc(p.Mem(), 1/2)
	if !(Point{x, y}.In(p.Rect)) {
		// @ fold acc(p.Mem(), 1/2)
		return Alpha16{}
	}
	// @ fold acc(p.Mem(), 1/2)
	i := p.PixOffset(x, y)
	// @ unfold acc(p.Mem(), 1/2)
	c = Alpha16{uint16(p.Pix[i+0])*256 + uint16(p.Pix[i+1])}
	// @ fold acc(p.Mem(), 1/2)
	return
}

// PixOffset returns the index of the first element of Pix that corresponds to
// the pixel at (x, y).
// @ requires acc(p.Mem(), 1/4)
// @ requires p.Inv()
// @ requires Point{x, y}.In(p.Bounds())
// @ ensures acc(p.Mem(), 1/4)
// @ ensures p.Inv()
// @ ensures unfolding acc(p.Mem(), 1/4) in 0 <= offset && offset < len(p.Pix)-1
func (p *Alpha16Image) PixOffset(x, y int) (offset int) {
	// @ unfold acc(p.Mem(), 1/4)
	offset = (y-p.Rect.Min.Y)*p.Stride + (x-p.Rect.Min.X)*2
	// @ LemmaMulPos(y-p.Rect.Min.Y, p.Rect.Max.Y-p.Rect.Min.Y-1, p.Stride)
	// @ fold acc(p.Mem(), 1/4)
	return
}

/*@
ghost
requires a <= b
requires c >= 0
ensures a * c <= b * c
decreases
func LemmaMulPos(a, b, c int) {}
@*/

// ANCHOR_END: Alpha16ImageMethods

// ANCHOR: Alpha16Client
func clientAlpha() {
	var i Image
	a := &Alpha16Image{
		Pix:    []uint8{0x0, 0x0, 0xff, 0xff, 0xff, 0xff, 0x0, 0x0},
		Stride: 4,
		Rect:   Rectangle{Point{0, 0}, Point{2, 2}},
	}
	// @ fold a.Mem()
	i = a
	i.ColorModel()
	// @ assert i.Inv()
	c := i.At(-1, 0)
	// @ assert(c.RGBASpec() == rgba{})
}

// ANCHOR_END: Alpha16Client

// ANCHOR_END: all
// @ (*Alpha16Image) implements Image
