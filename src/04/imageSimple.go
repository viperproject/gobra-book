// ANCHOR: all
package bounded

// ANCHOR: Bounded
type Bounded interface {
	// @ pred Mem()

	// ANCHOR: ImageBounds
	// @ preserves acc(Mem(), 1/2)
	Bounds() (r Rectangle)
	// ANCHOR_END: ImageBounds
}

type Point struct {
	X, Y int
}

type Rectangle struct {
	Min, Max Point
}

// ANCHOR_END: Bounded

// ANCHOR: Alpha16ImageImpl
// ANCHOR: Alpha16Image
type Alpha16Image struct {
	// Pix holds the image's pixels, as alpha values in big-endian format. The pixel at
	// (x, y) starts at Pix[(y-Rect.Min.Y)*Stride + (x-Rect.Min.X)*2].
	Pix []uint8
	// Stride is the Pix stride (in bytes) between vertically adjacent pixels.
	Stride int
	// Rect is the image's bounds.
	Rect Rectangle
}

// ANCHOR_END: Alpha16Image
/*@
pred (p *Alpha16Image) Mem() {
	acc(p) && forall i int :: {&p.Pix[i]} 0 <= i && i < len(p.Pix) ==> acc(&p.Pix[i])
}
@*/

// ANCHOR: Alpha16Bounds
// @ preserves acc(&p.Rect, 1/2)
func (p *Alpha16Image) Bounds() (r Rectangle) {
	return p.Rect
}

// ANCHOR_END: Alpha16Bounds

// ANCHOR_END: Alpha16ImageImpl

// ANCHOR: BoundsProof
/*@
(*Alpha16Image) implements Bounded {
	(p *Alpha16Image) Bounds() (r Rectangle) {
     	unfold acc(p.Mem(), 1/2)
        r = p.Bounds()
     	fold acc(p.Mem(), 1/2)
        return
    }
}
@*/
// ANCHOR_END: BoundsProof

func client(a *Alpha16Image) {
	var i Bounded = a
}

// ANCHOR_END: all
// ERROR property error: *Alpha16Image is not assignable to Bounded
// 	reason: *Alpha16Image has no member with name Bounds
// 	var i Bounded = a
//      ^
