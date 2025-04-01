/* ANCHOR: all */
package sharedarray

// ANCHOR: reverseInplace
const N = 10

// @ preserves forall i int :: 0 <= i && i < N ==> acc(&p[i])
// @ ensures forall i int :: 0 <= i && i < N ==> p[i] == old(p[N-i-1])
func reverseInplace(p *[N]int) {
	// @ invariant 0 <= i && i <= N / 2
	// @ invariant forall i int :: 0 <= i && i < N ==> acc(&p[i])
	// @ invariant forall j int :: 0 <= j && j < i ==> p[j] == old(p[N-j-1]) && p[N-j-1] == old(p[j])
	// @ invariant forall j int :: i <= j && j < N-i ==> p[j] == old(p[j])
	for i := 0; i < N/2; i += 1 {
		p[i], p[N-i-1] = p[N-i-1], p[i]
	}
}

// ANCHOR_END: reverseInplace

// ANCHOR: client1
func client1() {
	a /*@@@*/ := [10]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
	reverseInplace(&a)
	// @ assert a[0] == 9
	// @ assert a[9] == 0
}

// ANCHOR_END: client1

// ANCHOR: client2
// @ preserves acc(p)
// @ ensures *p == old(*p) + 1
func inc(p *int) {
	*p = *p + 1
}

func client2() {
	a /*@@@*/ := [10]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
	// @ assert acc(&a[0])
	inc(&a[0])
	// @ assert a[0] == 1
}

// ANCHOR_END: client2

// ANCHOR: client3
func client3() {
	a /*@@@*/ := [10]int{0, 1, 2, 3, 4, 5, 6, 7, 8, 9}
	p := &a
	// @ assert acc(p)
	// @ assert forall i int :: 0 <= i && i < N ==> acc(&p[i])
	r := reverse(a)
	// @ assert r[0] == 9 && r[9] == 0
	// @ assert a[0] == 0 && a[9] == 9
	// @ exhale acc(&a)
	r2 := reverse(a) // error
}

// ANCHOR_END: client3

// ANCHOR: reverse
// @ ensures forall i int :: {a[i]} {r[i]} 0 <= i && i < len(r) ==> r[i] == a[len(a)-i-1]
func reverse(a [N]int) (r [N]int) {
	// @ invariant 0 <= i && i <= len(a)
	// @ invariant forall j int :: 0 <= j && j < i ==> r[j] == a[len(a)-j-1]
	for i := 0; i < len(a); i += 1 {
		r[i] = a[len(a)-i-1]
	}
	return r
}

// ANCHOR_END: reverse

/* ANCHOR_END: all */
