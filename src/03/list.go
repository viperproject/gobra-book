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

// Returns the empty list.
// @ ensures l.Mem()
// @ ensures l.IsEmpty()
func Empty() (l *List) {
	l = (*List)(nil)
	// @ fold l.Mem()
	return
}

// ANCHOR: new
// New creates a new List node with the specified value and tail.
// @ requires tail.Mem()
// @ ensures out.Mem()
// @ ensures out.View() == seq[int]{value} ++ old(tail.View())
func New(value int, tail *List) (out *List) {
	out = &List{next: tail, Value: value}
	// @ fold out.Mem()
	return
}

// ANCHOR_END: new

// Tail returns a new list that is the tail of the original list,
// excluding the first element.
// @ requires l.Mem()
// @ requires !l.IsEmpty()
// @ ensures out.Mem()
// @ ensures out.View() == old(l.View()[1:])
func (l *List) Tail() (out *List) {
	// @ unfold l.Mem()
	out = l.next
	return
}

// ANCHOR: remove
// Remove returns the list with the element at index i deleted.
// @ requires l.Mem()
// @ requires 0 <= i && i < len(l.View())
// @ ensures out.Mem()
// @ ensures out.View() == old(l.View()[:i] ++ l.View()[i+1:])
func (l *List) Remove(i int) (out *List) {
	// @ unfold l.Mem()
	if i == 0 {
		return l.next
	}
	l.next = l.next.Remove(i - 1)
	// @ fold l.Mem()
	return l
}

// ANCHOR_END: remove

// ANCHOR: head
// Head returns the value of the first element in the list.
// @ pure
// @ requires acc(l.Mem(), 1/2)
// @ requires !l.IsEmpty()
// @ ensures value == l.View()[0]
// @ decreases
func (l *List) Head() (value int) {
	return /*@ unfolding acc(l.Mem(), 1/2) in @*/ l.Value
}

// ANCHOR_END: head

// ANCHOR: get
// Get returns the element at index i in the list.
// @ preserves acc(l.Mem(), 1/2)
// @ preserves 0 <= i && i < len(l.View())
// @ ensures value == l.View()[i]
// @ decreases l.Mem()
func (l *List) Get(i int) (value int) {
	// @ unfold acc(l.Mem(), 1/2)
	if i == 0 {
		value = l.Value
	} else {
		value = l.next.Get(i - 1)
	}
	// @ fold acc(l.Mem(), 1/2)
	return
}

// ANCHOR_END: get

// ANCHOR: isempty
// Returns true iff the list is empty.
// @ pure
// @ requires acc(l.Mem(), 1/2)
// @ ensures empty == (len(l.View()) == 0)
// @ decreases
func (l *List) IsEmpty() (empty bool) {
	return l == nil
}

// ANCHOR_END: isempty

// ANCHOR: length
// Returns the length of the list.
// @ preserves acc(l.Mem(), 1/2)
// @ ensures length == len(l.View())
// @ decreases l.Mem()
func (l *List) Length() (length int) {
	if l == nil {
		return 0
	} else {
		// @ unfold acc(l.Mem(), 1/2)
		length = 1 + l.next.Length()
		// @ fold acc(l.Mem(), 1/2)
		return length
	}
}

// ANCHOR_END: length

// ANCHOR: view
/*@
ghost
pure
requires acc(l.Mem(), 1/2)
decreases l.Mem()
func (l *List) View() seq[int] {
	return l == nil ? seq[int]{} : unfolding acc(l.Mem(), 1/2) in seq[int]{l.Value} ++ l.next.View()
}
@*/
// ANCHOR_END: view

// ANCHOR: client
func client() {
	ll := Empty()
	l0 := ll.Length()
	// @ assert l0 == 0
	ll = New(11, ll)
	// @ assert ll.Mem()
	// @ assert ll.Head() == 11
	// @ assert ll.View() == seq[int]{11}
	l1 := ll.Length()
	// @ assert l1 == 1
	ll = ll.Tail()
	// @ assert ll.View() == seq[int]{}
	ll = New(22, Empty())
	// @ assert ll.Head() == 22
	ll = New(33, ll)
	// @ assert ll.Head() == 33
	l2 := ll.Length()
	// @ assert l2 == 2
	v0 := ll.Get(0)
	v1 := ll.Get(1)
	// @ assert v0 == 33
	// @ assert v1 == 22
	ll := ll.Remove(1)
	l3 := ll.Length()
	// @ assert ll.Head() == 33
	// @ assert l3 == 1
}

// ANCHOR_END: client

/* ANCHOR_END: all */

// ANCHOR: pred
/*@
pred elements(l *List) {
	acc(&l.Value) && acc(&l.next) && (l.next != nil ==> elements(l.next))
}
@*/
// ANCHOR_END: pred

func folder0() {
	// ANCHOR: fold
	l := &List{Value: 1, next: nil}
	// @ assert acc(&l.Value) && acc(&l.next) && l.next == nil
	// @ assert acc(&l.Value) && acc(&l.next) && (l.next != nil ==> elements(l.next))

	// @ fold elements(l)

	// @ assert elements(l)

	v := l.Value // error
	// ANCHOR_END: fold
}

// ANCHOR: foldfail
// @ ensures elements(l)
func newFail(value int, tail *List) (l *List) {
	l := &List{Value: value, next: tail}
	// @ fold elements(l) // error
	return l
}

// ANCHOR_END: foldfail

// ANCHOR: foldsucceed
// @ requires tail != nil ==> elements(tail)
// @ ensures elements(l)
func newList(value int, tail *List) (l *List) {
	l := &List{Value: value, next: tail}
	// @ fold elements(l)
	return l
}

// ANCHOR_END: foldsucceed

func folder1() {
	// ANCHOR: unfold
	l := &List{Value: 1, next: nil}
	// @ fold elements(l)
	// @ assert elements(l)
	// @ unfold elements(l)
	// @ assert acc(&l.Value) && acc(&l.next) && (l.next != nil ==> elements(l.next))
	v := l.Value
	// ANCHOR_END: unfold
}

func folder2() {
	// ANCHOR: unfoldfail
	l := &List{Value: 1, next: nil}
	// @ fold elements(l)
	// @ unfold elements(l)
	// @ unfold elements(l) // error
	// ANCHOR_END: unfoldfail
}

func client1() {
	// ANCHOR: fold3
	l1 := &List{Value: 1, next: nil}
	// @ fold elements(l1)
	l2 := &List{Value: 2, next: l1}
	// @ fold elements(l2)
	l3 := &List{Value: 3, next: l2}
	// @ fold elements(l3)
	s := 0
	l := l3
	// @ assert elements(l)
	// @ invariant l != nil ==> elements(l)
	for l != nil {
		// @ unfold elements(l)
		s += l.Value
		l = l.next
	}
	// ANCHOR_END: fold3
}

// ANCHOR: fractional
func fractional() {
	l := New(1, Empty())
	// @ assert l.Mem()
	// @ assert acc(l.Mem())
	// @ assert acc(l.Mem(), 1)

	// @ unfold acc(l.Mem(), 1/2)
	// @ assert acc(l.Mem(), 1/2)
	// @ assert acc(l, 1/2) && acc(l.next.Mem(), 1/2)
	// @ fold acc(l.Mem(), 1/2)
	// @ assert l.Mem()
}

// ANCHOR_END: fractional

// ANCHOR: pred2
/*@
pred p2(l *List) {
	acc(&l.next, 1/2) && (l.next != nil ==> p2(l.next))
}
@*/

func client2() {
	l := &List{Value: 1, next: nil}
	// @ fold p2(l)
	// @ assert acc(p2(l), 1)
	// @ fold p2(l)
	// @ assert acc(p2(l), 2)
}

// ANCHOR_END: pred2

// ANCHOR: LengthIterative
// @ requires l.Mem()
// @ decreases l.Mem()
func (l *List) LengthIterative() (length int) {
	current := l
	// @ invariant current.Mem()
	// @ decreases current.Mem()
	for current != nil {
		// @ unfold current.Mem()
		length += 1
		current = current.next
	}
	return
}

// ANCHOR_END: LengthIterative

// ANCHOR: stream
/*@
pred stream(l *List) {
	acc(l) && stream(l.next)
}
@*/

// @ requires stream(l)
// @ decreases
func streaming(l *List) {
	a := 0
	// @ invariant stream(l)
	// @ decreases stream(l)
	for {
		// @ unfold stream(l)
		a += l.Value
		l = l.next
	}
}

// ANCHOR_END: stream
