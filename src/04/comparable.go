// ANCHOR: all
package main

// ANCHOR: type
type List struct {
	// Pointer to the next element in the linked list.
	next *List
	// The value stored with this element.
	Value interface{} // previously int
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

// ANCHOR: Comparable
/*@
ghost
requires acc(l.Mem(), 1/2)
pure
decreases l.Mem()
func (l *List) Comparable() bool {
	return l != nil ==> unfolding acc(l.Mem(), 1/2) in (isComparable(l.Value) && l.next.Comparable())
}
@*/
// ANCHOR_END: Comparable

// ANCHOR: Contains
// @ requires acc(l.Mem(), 1/2)
// @ requires l.Comparable()
// @ pure
// @ decreases l.Mem()
// ANCHOR: Contains1
func (l *List) Contains(value interface{}) bool {
	return /*@ unfolding acc(l.Mem(), 1/2) in @*/ l != nil && (l.Value == value || l.next.Contains(value))
}

// ANCHOR_END: Contains1
// ANCHOR_END: Contains

// ANCHOR: client
func client() {
	var l *List = nil
	// @ fold l.Mem()
	l = &List{Value: "hello", next: nil}
	// @ assert isComparable(l.Value)
	// @ fold l.Mem()
	l = &List{Value: 1, next: l}
	// @ fold l.Mem()
	// @ assert l.Contains("hello")
	// @ assert !l.Contains([2]int{0, 1})
}

// ANCHOR_END: client

// ANCHOR: isComparable
func compare(x any) {
	// @ assert !isComparable(type[[]int])
	// @ assert isComparable(type[string])
	x = 5
	// @ assert isComparable(x)
}

// ANCHOR_END: isComparable
// ANCHOR_END: all
// ANCHOR: main
func main() {
	var x any = []int{1, 2}
	var y any = []int{3}
	if x == y { // error
	}
}

// ANCHOR_END: main

// ANCHOR: GhostEq
// @ ghost
// @ decreases
// @ requires 0 <= i && i < len(s)
// @ requires 0 <= j && j < len(s)
// @ requires s[i] === s[j]
// @ func GhostEq(s seq[any], i, j int) {}
// ANCHOR_END: GhostEq
