/* ANCHOR: all */
package list

// ANCHOR: type
type List struct {
	// Pointer to the next element in the linked list.
	next *List
	// The value stored with this element.
	Value int
}

// ANCHOR_END: type

// ANCHOR: mem
/*@
// Represents access to the List element and all elements in its tail.
pred (l *List) Mem() {
	l != nil ==> (acc(l) && l.next.Mem())
}
@*/
// ANCHOR_END: mem

// ANCHOR: empty
// Returns the empty list.
// @ ensures l.Mem()
// @ ensures l.IsEmpty()
func Empty() (l *List) {
	l = (*List)(nil)
	// @ fold l.Mem()
	return
}

// ANCHOR_END: empty

// ANCHOR: new
// New creates a new List node with the specified value and tail.
// @ requires tail.Mem()
// @ ensures out.Mem()
// @ ensures !out.IsEmpty()
// @ ensures out.Head() == value
func New(value int, tail *List) (out *List) {
	out = &List{next: tail, Value: value}
	// @ fold out.Mem()
	return
}

// ANCHOR_END: new

// ANCHOR: head
// Head returns the value of the first element in the list.
// @ pure
// @ requires l.Mem()
// @ requires !l.IsEmpty()
// @ decreases
func (l *List) Head() (value int) {
	return /*@ unfolding l.Mem() in @*/ l.Value
}

// ANCHOR_END: head

// ANCHOR: isempty
// Returns true iff the list is empty.
// @ pure
// @ requires l.Mem()
// @ decreases
func (l *List) IsEmpty() (empty bool) {
	return l == nil
}

// ANCHOR_END: isempty

// ANCHOR: client
func client() {
	e := Empty()
	// @ assert e.Mem()
	// @ assert e.IsEmpty()
	l1 := New(11, e)
	// @ assert l1.Mem()
	// @ assert l1.Head() == 11
	l2 := New(22, Empty())
	// @ assert l2.Head() == 22
	l3 := New(33, l2)
	// @ assert l3.Head() == 33
}

// ANCHOR_END: client

/* ANCHOR_END: all */

// ANCHOR: newbad
// @ ensures acc(&out.Value) && acc(&out.next)
// @ ensures out.next == tail
// @ ensures out.Value == value
func NewBad(value int, tail *List) (out *List) {
	out = &List{next: tail, Value: value}
	return
}

// ANCHOR_END: newbad
