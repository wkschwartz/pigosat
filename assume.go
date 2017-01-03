// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

// #include "picosat.h"
import "C"
import "unsafe"

// For testing litArrayToSlice in TestlitArrayToSlice since you can't import CGo
// into test files.
var cArray123 = [3]C.int{1, 2, 3}
var cArray1230 = [4]C.int{1, 2, 3, 0}
var cZero C.int = 0

// Assume adds a unit clause (i.e., a clause containing one literal) containing
// just the given literal for just the next call to Solve. You can add arbitrary
// many assumptions before the next Solve. After the next call to Solve, the
// assumptions are removed.
//
// More precisely, assumptions actually remain valid even after the next call to
// Solve() returns. Valid means they remain 'assumed' until a call to
// AddClauses(), Assume(), or another Solve(), following the first Solve().
// They need to stay valid for FailedAssumptions(), etc., to work correctly.
//
// Example:
//
//   p.Assume(1)                // assume unit clause Clause{1, 0}
//   p.Assume(-2)               // additionally assume unit clause Clause{-2, 0}
//   res, solution := p.Solve() // assumes 1 and -2 to hold
//
//   if res == Unsatisfiable {
//       if p.FailedAssumption(1) {
//           // unit clause Clause{1, 0} was necessary to derive Unsatisfiable
//       }
//       if p.FailedAssumption(-2) {
//           // unit clause Clause{-2, 0} was necessary to derive Unsatisfiable
//       }
//       // at least one but also both could be necessary
//
//       p.Assume(17)  // Previous assumptions are removed. Now assume unit
//                     // clause Clause{17, 0} for the next call to Solve().
//
//   } else if res == Satisfiable {
//       // The assumptions 1 and -2 hold, so the follow assertion succeeds.
//       if !(solution[1] && !solution[2]) {
//           panic("assertion failed")
//       }
//
//       // Assumptions valid, as always, until calls to AddClauses(), etc.
//       // Further, when entering Solve() the solver knows that the previous
//       // call returned SAT and it can safely reset the previous assumptions.
//   } else  {
//       // res == Unknown
//
//       // Assumptions valid, but assignment invalid except for top level
//       // assigned literals which necessarily need to have this value if the
//       // formula is SAT
//
//       // As above the solver knows that the previous call returned Unknown
//       // and will reset assumptions before doing anything else.
//   }
func (p *Pigosat) Assume(lit Literal) {
	defer p.ready(false)()
	// void picosat_assume (PicoSAT *, int lit);
	C.picosat_assume(p.p, C.int(lit))
}

// FailedAssumption returns true if the literal is a failed assumption, meaning
// the literal was added with Assume then used to derive unsatisfiability.
// The return value is only meaningful as long the current assumptions are
// valid. See Assume() for more details.
//
// From the Picosat documentation:
//   This is as accurate as generating core literals, but still of course is an
//   overapproximation of the set of assumptions really necessary. The technique
//   does not need clausal core generation nor tracing to be enabled and thus
//   can be much more effective.
func (p *Pigosat) FailedAssumption(lit Literal) bool {
	defer p.ready(true)()
	// picoast_failed_assumption SIGABRTs if the following conditional is true
	if p.res() != Unsatisfiable || lit == 0 {
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
		if len(lits) > maxLen {
			panic("Array not zero-terminated")
		}
		lits = append(lits, Literal(*litPtr))
		litPtr = (*C.int)(unsafe.Pointer(
			uintptr(unsafe.Pointer(litPtr)) + uintptr(C.sizeof_int)))
	}
	return lits
}

// FailedAssumptions returns a list of failed assumptions in the last call to
// Solve() or an empty list if the last call to Solve() did not return
// Unsatisfiable. See Assume() and FailedAssumption() for more details.
func (p *Pigosat) FailedAssumptions() []Literal {
	defer p.ready(true)()
	if p.res() != Unsatisfiable {
		return []Literal{}
	}

	// const int * picosat_failed_assumptions (PicoSAT *);
	litPtr := C.picosat_failed_assumptions(p.p)
	return litArrayToSlice(litPtr, int(C.picosat_variables(p.p)))
}

// MaxSatisfiableAssumptions computes a maximal subset of satisfiable
// assumptions. See Assume() for more details. You need to set the assumptions
// and call Solve() before calling this function. The result is a list of
// assumptions that consistently can be asserted at the same time.
//
// It could be beneficial to set the default phase of assumptions
// to true (positive). This can speed up the computation.
func (p *Pigosat) MaxSatisfiableAssumptions() []Literal {
	defer p.ready(false)()
	if C.picosat_inconsistent(p.p) != 0 {
		return []Literal{}
	}
	//const int * picosat_maximal_satisfiable_subset_of_assumptions (PicoSAT *);
	litPtr := C.picosat_maximal_satisfiable_subset_of_assumptions(p.p)
	return litArrayToSlice(litPtr, int(C.picosat_variables(p.p)))
}

// This function assumes that you have set up all assumptions with
// 'Assume()'.  Then it calls 'Solve()' internally unless the
// formula is already inconsistent without assumptions, i.e.  it contains
// the empty clause.  After that it extracts a maximal satisfiable subset of
// assumptions.
//
// The result is a zero terminated maximal subset of consistent assumptions
// or an empty list if the formula contains the empty clause and thus no
// more maximal consistent subsets of assumptions can be extracted.  In the
// first case, before returning, a blocking clause is added, that rules out
// the result for the next call.
//
// NOTE: adding the blocking clause changes the CNF.
//
// So the following idiom
//
// var lits []Literal;
// p.Assume(a1)
// p.Assume(a2)
// p.Assume(a3)
// p.Assume(a4)
// for mss := p.NextMaxSatisfiableAssumptions(); len(mss) > 0; mss = p.NextMaxSatisfiableAssumptions() {
//     ProcessResults(mss)
// }
//
// can be used to iterate over all maximal consistent subsets of
// the set of assumptions {a1,a2,a3,a4}.
//
// It could be beneficial to set the default phase of assumptions
// to true (positive). This might speed up the computation.
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
