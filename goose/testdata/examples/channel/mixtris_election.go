package channel_examples

// Three-way leader election, from the Mixtris paper (§2.4).
//
// Three participants are arranged in a ring. Each one races to either send to
// its clockwise neighbour or receive from its counter-clockwise neighbour,
// using a mixed-choice select. Mixed choice guarantees that at most one of the
// three possible exchanges happens, so at most one participant is elected.
//
// The elected leader announces itself by closing done. Closing an
// already-closed channel panics, so this program is safe exactly when the
// election elects at most one leader -- which is what the Hoare triple
// {True} ThreeWayElection {True} certifies, via adequacy. It plays the role of
// the paper's `free l`, whose safety likewise rests on being reached once.
func ThreeWayElectionParty(send chan uint64, recv chan uint64, id uint64, done chan uint64) {
	select {
	case send <- id:
		// Not elected: somebody downstream took our message.
	case <-recv:
		// Elected: we hold the only permission to close done.
		close(done)
	}
}

func ThreeWayElection() {
	// One Go channel per directed edge of the ring, rather than the 3x3
	// matrix of synchronisation cells the paper's implementation allocates.
	ab := make(chan uint64)
	bc := make(chan uint64)
	ca := make(chan uint64)
	done := make(chan uint64)
	go ThreeWayElectionParty(ab, ca, 0, done)
	go ThreeWayElectionParty(bc, ab, 1, done)
	go ThreeWayElectionParty(ca, bc, 2, done)
}
