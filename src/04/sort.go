// ANCHOR: all
package sort

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

// ANCHOR: client
func client() {
	var x Interface
	var s IntSlice = []int{1, 2, 2}
	// @ fold s.Mem()
	// @ assert len(s) == 3
	x = s
	b := IsSorted(x)
	// @ assert b
	// @ assert len(x.View()) == 3

	// @ assert x.LessSpec(0, 1)
	// @ assert !x.LessSpec(1, 2)
	// @ assert x.LessSpec(0, 2)
	// @ assert x.View()[1] == x.View()[2]
	// @ assert typeOf(x.View()[1]) == type[int]

	if v, ok := x.(IntSlice); ok {
		// @ assert len(v) == 3
	} else {
		// @ assert false
	}

}

// ANCHOR_END: client

// ANCHOR: IsSorted
// IsSorted reports whether data is sorted.
// @ requires data != nil
// @ requires acc(data.Mem(), 1/2)
// @ ensures acc(data.Mem(), 1/2)
// @ ensures res == forall j int :: {data.LessSpec(j, j-1)} 0 < j && j < len(data.View()) ==> !data.LessSpec(j, j-1)
// @ decreases
func IsSorted(data Interface) (res bool) {
	n := data.Len()
	if n <= 1 { // added if s.t. the loop invariant can be established
		return true
	}
	// @ invariant acc(data.Mem(), 1/2)
	// @ invariant 0 <= i && i < len(data.View())
	// @ invariant forall j int :: {data.LessSpec(j, j-1)} i < j && j < len(data.View()) ==> !data.LessSpec(j, j-1)
	// @ decreases i
	for i := n - 1; i > 0; i-- {
		if data.Less(i, i-1) {
			return false
		}
	}
	return true
}

// ANCHOR_END: IsSorted
// --------- Interface -----------
// ANCHOR: Interface
// https://cs.opensource.google/go/go/+/refs/tags/go1.23.6:src/sort/sort.go;l=118

type Interface interface {
	// @ pred Mem()

	// @ ghost
	// @ requires acc(Mem(), _)
	// @ decreases
	// @ pure View() (ghost seq[any])

	// Len is the number of elements in the collection.
	// @ requires acc(Mem(), 1/1024)
	// @ ensures acc(Mem(), 1/1024)
	// @ ensures res == len(View())
	// @ decreases len(View())
	Len() (res int)

	// ANCHOR: LessDoc
	// Less reports whether the element with index i
	// must sort before the element with index j.
	//
	// If both Less(i, j) and Less(j, i) are false,
	// then the elements at index i and j are considered equal.
	// Sort may place equal elements in any order in the final result,
	// while Stable preserves the original input order of equal elements.
	//
	// Less must describe a transitive ordering:
	// - if both Less(i, j) and Less(j, k) are true, then Less(i, k) must be true as well.
	// - if both Less(i, j) and Less(j, k) are false, then Less(i, k) must be false as well.
	//
	// ANCHOR_END: LessDoc
	// Note that floating-point comparison (the < operator on float32 or float64 values)
	// is not a transitive ordering when not-a-number (NaN) values are involved.
	// See Float64Slice.Less for a correct implementation for floating-point values.
	// @ ghost
	// @ requires acc(Mem(), _)
	// @ requires 0 <= i && i < len(View())
	// @ requires 0 <= j && j < len(View())
	// @ decreases len(View())
	// @ pure LessSpec(i, j int) bool

	// @ requires acc(Mem(), 1/1024)
	// @ requires 0 <= i && i < len(View())
	// @ requires 0 <= j && j < len(View())
	// @ ensures acc(Mem(), 1/1024)
	// @ ensures res == old(LessSpec(i, j))
	// @ decreases len(View())
	Less(i, j int) (res bool)

	// ANCHOR: InterfaceLessIsConnected
	// @ ghost
	// @ requires acc(Mem(), _)
	// @ requires 0 <= i && i < len(View())
	// @ requires 0 <= j && j < len(View())
	// @ requires !LessSpec(i, j)
	// @ requires !LessSpec(j, i)
	// @ ensures acc(Mem(), _)
	// @ ensures let view := old(View()) in view[i] === view[j]
	// @ decreases
	// @ LessIsConnected(i, j int)
	// ANCHOR_END: InterfaceLessIsConnected

	// ANCHOR: InterfaceLessIsTransitive
	// @ ghost
	// @ requires acc(Mem(), _)
	// @ requires 0 <= i && i < len(View())
	// @ requires 0 <= j && j < len(View())
	// @ requires 0 <= k && k < len(View())
	// @ requires LessSpec(i, j) && LessSpec(j, k)
	// @ ensures acc(Mem(), _)
	// @ ensures old(LessSpec(i, k))
	// @ decreases
	// @ LessIsTransitive(i, j, k int)
	// ANCHOR_END: InterfaceLessIsTransitive

	// ANCHOR: InterfaceSwap
	// Swap swaps the elements with indices i and j.
	// @ requires acc(Mem(), 1)
	// @ requires 0 <= i && i < len(View())
	// @ requires 0 <= j && j < len(View())
	// @ ensures acc(Mem(), 1)
	// @ ensures let oldView := old(View()) in
	// @ 	let oldi := oldView[i] in
	// @ 	let oldj := oldView[j] in
	// @ 	View() == oldView[i = oldj][j = oldi]
	// @ decreases len(View())
	Swap(i, j int)
	// ANCHOR_END: InterfaceSwap
}

// ANCHOR_END: Interface
// --------- Implementation -----------
// ANCHOR: IntSlice

// ANCHOR: IntSliceType
type IntSlice []int

// ANCHOR_END: IntSliceType

// ANCHOR: IntSliceMem
/*@
pred (s IntSlice) Mem() {
	acc(s)
}
@*/
// ANCHOR_END: IntSliceMem

// ANCHOR: IntSliceView
/*@
ghost
requires acc(s.Mem(), _)
ensures len(res) == len(s)
ensures forall i int :: {res[i]} {s[i]} 0 <= i && i < len(res) ==> unfolding acc(s.Mem(), _) in  res[i] == s[i]
decreases
pure func (s IntSlice) View() (ghost res seq[any]) {
	return unfolding acc(s.Mem(), _) in s.viewAux(0, seq[any]{})
}
@*/

/*@
ghost
requires acc(s, _)
requires 0 <= i && i <= len(s)
requires len(prefix) == i
ensures len(res) == len(s)
requires forall i int :: {prefix[i]} {s[i]} 0 <= i && i < len(prefix) ==> prefix[i] == s[i]
ensures forall i int :: {res[i]} 0 <= i && i < len(res) ==> res[i] == s[i]
decreases len(s) - i
pure
func (s IntSlice) viewAux(i int, prefix seq[any]) (ghost res seq[any]) {
    return i == len(s) ? prefix : s.viewAux(i + 1, prefix ++ seq[any]{s[i]})
}
@*/
// ANCHOR_END: IntSliceView

// ANCHOR: IntSliceLen
// @ requires acc(s.Mem(), 1/1024)
// @ ensures acc(s.Mem(), 1/1024)
// @ ensures res == len(s.View())
// @ decreases
func (s IntSlice) Len() (res int) {
	// @ unfold acc(s.Mem(), 1/1024)
	res = len(s)
	// @ fold acc(s.Mem(), 1/1024)
	return
}

// ANCHOR_END: IntSliceLen
// ANCHOR: IntSliceLess
/*@
ghost
requires acc(s.Mem(), _)
requires 0 <= i && i < len(s.View())
requires 0 <= j && j < len(s.View())
decreases len(s.View())
pure func (s IntSlice) LessSpec(i, j int) (res bool) {
	return unfolding acc(s.Mem(), _) in s[i] < s[j]
}
@*/

// @ requires acc(s.Mem(), 1/1024)
// @ requires 0 <= i && i < len(s.View())
// @ requires 0 <= j && j < len(s.View())
// @ ensures acc(s.Mem(), 1/1024)
// @ ensures res == old(s.LessSpec(i, j))
// @ decreases
func (s IntSlice) Less(i, j int) (res bool) {
	// @ unfold acc(s.Mem(), 1/1024)
	res = s[i] < s[j]
	// @ fold acc(s.Mem(), 1/1024)
}

/*@
ghost
requires acc(s.Mem(), _)
requires 0 <= i && i < len(s.View())
requires 0 <= j && j < len(s.View())
requires !s.LessSpec(i, j) && !s.LessSpec(j, i)
ensures acc(s.Mem(), _)
ensures let view := s.View() in view[i] === view[j]
decreases
func (s IntSlice) LessIsConnected(i, j int) {}
@*/

/*@
ghost
requires acc(s.Mem(), _)
requires 0 <= i && i < len(s.View())
requires 0 <= j && j < len(s.View())
requires 0 <= k && k < len(s.View())
requires s.LessSpec(i, j) && s.LessSpec(j, k)
ensures acc(s.Mem(), _)
ensures s.LessSpec(i, k)
decreases
func (s IntSlice) LessIsTransitive(i, j, k int) {}
@*/
// ANCHOR_END: IntSliceLess

// ANCHOR: IntSliceSwap
// @ requires acc(s.Mem(), 1)
// @ requires 0 <= i && i < len(s.View())
// @ requires 0 <= j && j < len(s.View())
// @ ensures acc(s.Mem(), 1)
// @ ensures let oldView := old(s.View()) in
// @ 	let oldi := oldView[i] in
// @ 	let oldj := oldView[j] in
// @ 	s.View() == oldView[i = oldj][j = oldi]
// @ decreases
func (s IntSlice) Swap(i, j int) {
	// @ unfold acc(s.Mem(), 1)
	s[i], s[j] = s[j], s[i]
	// @ fold acc(s.Mem(), 1)
}

// ANCHOR_END: IntSliceSwap
// ANCHOR_END: IntSlice
// ANCHOR: IntSliceImplements
// @ IntSlice implements Interface
// ANCHOR_END: IntSliceImplements

// ANCHOR_END: all
