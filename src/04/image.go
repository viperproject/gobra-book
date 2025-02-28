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
// Color can convert itself to alpha-premultiplied 16-bits per channel RGBA.
// The conversion may be lossy.
type Color interface {
	// RGBA returns the alpha-premultiplied red, green, blue and alpha values
	// for the color. Each value ranges within [0, 0xffff], but is represented
	// by a uint32 so that multiplying by a blend factor up to 0xffff will not
	// overflow.
	//
	// An alpha-premultiplied color component c has been scaled by alpha (a),
	// so has valid values 0 <= c <= a.
	// @ ensures r <= 0xffff && g <= 0xffff && b <= 0xffff && a <= 0xffff
	// @ ensures 0 <= r && r <= a && 0 <= g && g <= a && 0 <= b && b <= a
	RGBA() (r, g, b, a uint32)
}

// source: https://cs.opensource.google/go/go/+/refs/tags/go1.24.0:src/image/color/color.go;l=10
// ANCHOR_END: Color

// ANCHOR: Alpha16
// Alpha16 represents a 16-bit alpha color.
type Alpha16 struct {
	A uint16
}

// @ ensures r <= 0xffff && g <= 0xffff && b <= 0xffff && a <= 0xffff
// @ ensures 0 <= r && r <= a && 0 <= g && g <= a && 0 <= b && b <= a
func (c Alpha16) RGBA() (r, g, b, a uint32) {
	// TODO: can we do this without the inhale?
	// @ inhale 0 <= c.A && c.A <= 0xffff // c.A : uint16
	a = uint32(c.A)
	return a, a, a, a
}

// ANCHOR_END: Alpha16

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

func client1Constant() {
	var c Color
	c = Constant{}
	r, _, _, a := c.RGBA()
	// @ assert 0 <= a && r <= a
}

// ANCHOR_END: Constant
// @ Constant implements Color

// ANCHOR: Model
// Model can convert any [Color] to one from its own color model. The conversion
// may be lossy.
type Model interface {
	// @ requires c != nil
	Convert(c Color) Color
}

// ANCHOR_END: Model

// TODO can we better represent this?
// Go stdlib uses the following, which is not legal in Gobra.
// var Alpha16Model Model = ModelFunc(alpha16Model)

// ANCHOR: alpha16Model
type alpha16Model struct{}

var Alpha16Model alpha16Model

// @ requires c != nil
// @ ensures typeOf(res) == type[Alpha16]
func (_ alpha16Model) Convert(c Color) (res Color) {
	if _, ok := c.(Alpha16); ok {
		return c
	}
	_, _, _, a := c.RGBA()
	return Alpha16{uint16(a)}
}

// ANCHOR_END: alpha16Model

// ANCHOR: Geometry
// A Point is an X, Y coordinate pair. The axes increase right and down.
type Point struct {
	X, Y int
}

/*@
pure
decreases
func (p Point) InSpec(r Rectangle) bool {
	return r.Min.X <= p.X && p.X < r.Max.X &&
		r.Min.Y <= p.Y && p.Y < r.Max.Y
}
@*/

// In reports whether p is in r.
// @ ensures res == p.InSpec(r)
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
// Image is a finite rectangular grid of [color.Color] values taken from a color
// model.
type Image interface {
	// Mem represents the access to the memory of the Image
	// @ pred Mem()

	// @ ghost
	// @ pure
	// @ requires acc(Mem(), 1/2)
	// @ decreases
	// @ Inv() bool

	// ColorModel returns the Image's color model.
	ColorModel() Model // color.Model
	// ANCHOR: ImageBounds
	// Bounds returns the domain for which At can return non-zero color.
	// The bounds do not necessarily contain the point (0, 0).
	// @ preserves acc(Mem(), 1/2)
	// @ preserves Inv()
	Bounds() (r Rectangle)
	// ANCHOR_END: ImageBounds
	// At returns the color of the pixel at (x, y).
	// At(Bounds().Min.X, Bounds().Min.Y) returns the upper-left pixel of the grid.
	// At(Bounds().Max.X-1, Bounds().Max.Y-1) returns the lower-right one.

	// @ preserves acc(Mem(), 1/2)
	// @ preserves Inv()
	At(x, y int) Color // color.Color
}

// ANCHOR_END: Image

// ANCHOR: RectImpl
// ANCHOR: standard
var (
	Transparent = Alpha16{0}
	Opaque      = Alpha16{0xffff}
)

// ANCHOR_END: standard
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
func (r Rectangle) ColorModel() Model {
	return Alpha16Model
}

// Bounds implements the [Image] interface.
// @ preserves acc(r.Mem(), 1/2)
// @ preserves r.Inv()
func (r Rectangle) Bounds() Rectangle {
	return r
}

// At implements the [Image] interface.
// @ preserves acc(r.Mem(), 1/2)
// @ preserves r.Inv()
func (r Rectangle) At(x, y int) (c Color) {
	if (Point{x, y}).In(r) {
		return Opaque
	}
	return Transparent
}

// ANCHOR_END: RectImpl
// @ Rectangle implements Image

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
requires acc(p.Mem(), 1/2)
pure
decreases
func (p *Alpha16Image) Inv() bool {
	return unfolding acc(p.Mem(), 1/2) in (2 * (p.Rect.Max.X - p.Rect.Min.X) == p.Stride && p.Stride * (p.Rect.Max.Y - p.Rect.Min.Y) == len(p.Pix))
}
@*/
// ANCHOR_END: Alpha16ImageInv

// ANCHOR: Alpha16ImageMethods

func (p *Alpha16Image) ColorModel() Model { return Alpha16Model }

// @ preserves acc(p.Mem(), 1/2)
// @ preserves p.Inv()
func (p *Alpha16Image) Bounds() (r Rectangle) {
	// @ unfold acc(p.Mem(), 1/2)
	r = p.Rect
	// @ fold acc(p.Mem(), 1/2)
	return
}

// @ requires acc(p.Mem(), 1/2)
// @ requires p.Inv()
// @ ensures acc(p.Mem(), 1/2)
// @ ensures p.Inv()
func (p *Alpha16Image) At(x, y int) (res Color) {
	// @ unfold acc(p.Mem(), 1/2)
	if !(Point{x, y}.In(p.Rect)) {
		// @ fold acc(p.Mem(), 1/2)
		return Alpha16{}
	}
	// @ fold acc(p.Mem(), 1/2)
	i := p.PixOffset(x, y)
	// @ unfold acc(p.Mem(), 1/2)
	// @ assert 0 <= i && i < len(p.Pix)
	res = Alpha16{uint16(p.Pix[i+0])<<8 | uint16(p.Pix[i+1])}
	// @ fold acc(p.Mem(), 1/2)
	return
}

// PixOffset returns the index of the first element of Pix that corresponds to
// the pixel at (x, y).
// @ requires acc(p.Mem(), 1/2)
// @ requires unfolding acc(p.Mem(), 1/2) in Point{x, y}.InSpec(p.Rect)
// @ requires p.Inv()
// @ ensures acc(p.Mem(), 1/2)
// @ ensures p.Inv()
// @ ensures unfolding acc(p.Mem(), 1/2) in 0 <= offset && offset < len(p.Pix) - 1
func (p *Alpha16Image) PixOffset(x, y int) (offset int) {
	// @ unfold acc(p.Mem(), 1/2)
	offset = (y-p.Rect.Min.Y)*p.Stride + (x-p.Rect.Min.X)*2
	// @ ghost var height = p.Rect.Max.Y - p.Rect.Min.Y
	// @ ghost var dy = y-p.Rect.Min.Y
	// @ ghost var dx = (x-p.Rect.Min.X) * 2
	// @ assert offset == dy * p.Stride + dx
	// @ assert 0 <= dx && 0 <= dy && 0 <= offset
	// @ assert dy <= height - 1
	// @ assert dx <= p.Stride - 2
	// @ LemmaMulPos(dy, height - 1, p.Stride)
	// @ assert dy * p.Stride <= (height - 1) * p.Stride
	// @ assert dy * p.Stride + dx <= (height - 1) * p.Stride + dx
	// @ assert offset <= (height - 1) * p.Stride + p.Stride - 2
	// @ assert offset <= height * p.Stride - 2
	// @ assert offset <= len(p.Pix) - 2
	// @ fold acc(p.Mem(), 1/2)
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

// @ (*Alpha16Image) implements Image

// ANCHOR_END: all
