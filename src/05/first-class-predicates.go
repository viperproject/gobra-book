// ANCHOR: all
package main

// ANCHOR: Pred
/*@
pred Mem(x *int8, y *uint32) {
	acc(x) && acc(y)
}
@*/
// ANCHOR_END: Pred

// ANCHOR: Pred2
/*@
pred OtherMem(x *int8, y *uint32) {
	acc(x) && acc(y)
}
@*/
// ANCHOR_END: Pred2

// ANCHOR: Eq
// @ requires a == b
func client1(a, b *int8, c *uint32) {
	// @ assert Mem!<a, _!> == Mem!<b, _!>
	// @ assert Mem!<a, c!> == Mem!<b, c!>
	// @ assert OtherMem!<a, c!> == Mem!<a, c!> // error
}

// ANCHOR_END: Eq

// ANCHOR: fold
// @ preserves Mem!<x, y!>()
func client2(x *int8, y *uint32) {
	// @ unfold Mem!<x, y!>()
	*x = 1
	*y = 2
	// @ fold Mem!<x, y!>()
}

// ANCHOR_END: fold

func construct() {
	// @ p := Mem!<_, new(uint32)!>
}

// ANCHOR: param
func client() {
	x := new(int8)
	y := new(uint32)
	// @ setPredicate(Mem!<x, y!>)
}

// ANCHOR_END: param

/*@
// ANCHOR: setPredicate
ghost
decreases
func setPredicate(p pred()) {}
@*/
// ANCHOR_END: setPredicate
// ANCHOR_END: all
