package frame

// ANCHOR: inc_full
// @ requires acc(p)
// ANCHOR: inc
func inc(p *int) {
	*p = *p + 1
}

// ANCHOR_END: inc
// ANCHOR_END: inc_full

// ANCHOR: client_full
// @ requires acc(x) && acc(y)
// ANCHOR: client
func client(x, y *int) {
	snapshotX := *x
	snapshotY := *y
	inc(y)
	// @ assert snapshotX == *x
}

// ANCHOR_END: client
// ANCHOR_END: client_full

// ANCHOR: driver
// @ requires acc(p)
func driver(p *int) {
	go inc(p)
	go inc(p) // error
}

// ANCHOR_END: driver
