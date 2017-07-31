// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

// #include "picosat.h"
import "C"
import "unsafe"

// For testing litArrayToSlice in TestlitArrayToSlice since you can't import CGo
// into test files.
var cArray123 = [3]C.int{1, 2, 3}
var cArray1230 = [4]C.int{1, 2, 3, 0}
var cZero C.int

// Assume adds a temporary unit clause, i.e., a clause containing the one
// literal you pass as an argument. An assumption remains valid after the next
// call to Solve returns until a call to Add, Assume, or a second Solve. You can
// add arbitrary many assumptions before the next call to Solve. Methods
// FailedAssumptions, FailedAssumptions, MaxSatisfiableAssumptions, and
// NextMaxSatisfiableAssumptions operate on the current, valid assumptions.
func (p *Pigosat) Assume(lit Literal) {
	defer p.ready(false)()
	p.couldHaveFailedAssumptions = false
	// void picosat_assume (PicoSAT *, int lit);
	C.picosat_assume(p.p, C.int(lit))
}

// FailedAssumption returns whether a given literal is a valid, "failed"
// assumption (see Assume), meaning the last call to Solve used the assumption
// to derive unsatisfiability. FailedAssumption always returns false when the
// last call to Solve had status other than Unsatisfiable. This may be an
// over-approximation of the set of assumptions necessary to derive
// unsatisfiability.
func (p *Pigosat) FailedAssumption(lit Literal) bool {
	defer p.ready(true)()
	// picoast_failed_assumption SIGABRTs if the following conditional is true
	if p.res() != Unsatisfiable || lit == 0 || !p.couldHaveFailedAssumptions {
		return false
	}
	// int picosat_failed_assumption (PicoSAT *, int lit);
	return C.picosat_failed_assumption(p.p, C.int(lit)) != 0
}

// litArrayToSlice converts a 0-terminated C array of ints (of length at most
// maxLen) to a Go slice of Literals.
func litArrayToSlice(litPtr *C.int, maxLen int) []Literal {
	if litPtr == nil {
		panic("NULL pointer")
	}
	lits := []Literal{}
	for *litPtr != 0 {
		if len(lits) >= maxLen {
			panic("The array's length is greater than the maxLen parameter.")
		}
		lits = append(lits, Literal(*litPtr))
		litPtr = (*C.int)(unsafe.Pointer(
			uintptr(unsafe.Pointer(litPtr)) + uintptr(C.sizeof_int)))
	}
	return lits
}

// FailedAssumptions returns a list of failed assumptions, i.e., all the
// for which FailedAssumption returns true. See FailedAssumption.
func (p *Pigosat) FailedAssumptions() []Literal {
	defer p.ready(false)() // Overwrites what becomes litPtr below.
	if p.res() != Unsatisfiable || !p.couldHaveFailedAssumptions {
		return []Literal{}
	}

	// const int * picosat_failed_assumptions (PicoSAT *);
	litPtr := C.picosat_failed_assumptions(p.p)
	return litArrayToSlice(litPtr, int(C.picosat_variables(p.p)))
}

// MaxSatisfiableAssumptions computes a maximal subset of satisfiable
// assumptions. See Assume's documentation. You need to set the assumptions
// and call Solve() before calling this method. The result is a list of
// assumptions that consistently can be asserted at the same time.
func (p *Pigosat) MaxSatisfiableAssumptions() []Literal {
	defer p.ready(false)()
	if C.picosat_inconsistent(p.p) != 0 {
		return []Literal{}
	}
	// const int * picosat_maximal_satisfiable_subset_of_assumptions (PicoSAT *);
	litPtr := C.picosat_maximal_satisfiable_subset_of_assumptions(p.p)
	return litArrayToSlice(litPtr, int(C.picosat_variables(p.p)))
}

// NextMaxSatisfiableAssumptions is like MaxSatisfiableAssumptions, but operates
// like an iterator to give a different maximal subset of satisfiable
// assumptions upon each call. To do this, it internally calls Solve followed by
// BlockSolution, which modifies the underlying formula (thus changing the
// result of AddedOriginalClauses), and then reassuming the solutions that were
// valid when you called NextMaxSatisfiableAssumptions. Use it as follows.
// First, set your formula and assumptions using Add and Assume. Then iterate
// over the different maximal satisfiable subsets of assumptions with:
//    for mss := p.NextMaxSatisfiableAssumptions(); len(mss) > 0; mss = p.NextMaxSatisfiableAssumptions() {
//        // Do stuff with mss
//    }
func (p *Pigosat) NextMaxSatisfiableAssumptions() []Literal {
	defer p.ready(false)()
	if C.picosat_inconsistent(p.p) != 0 {
		return []Literal{}
	}
	// const int *
	// picosat_next_maximal_satisfiable_subset_of_assumptions (PicoSAT *);
	litPtr := C.picosat_next_maximal_satisfiable_subset_of_assumptions(p.p)
	return litArrayToSlice(litPtr, int(C.picosat_variables(p.p)))
}
