package ghostpure

const N = 42

/*@
ghost
requires forall i int :: 0 <= i && i < len(*s) ==> acc(&s[i], _)
decreases
pure func allZero(s *[N]int) bool {
    return forall i int :: 0 <= i && i < len(*s) ==> s[i] == 0
}
@*/

func client() {
	xs := new([N]int)
	// @ assert acc(xs, 1)
	// @ assert allZero(xs)
	// @ assert acc(xs, 1)
}
