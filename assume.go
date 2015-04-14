// assume.go defines Pigosat methods related to PicoSAT assumptions

package pigosat

// #include "picosat.h"
import "C"
import (
	"reflect"
	"unsafe"
)

// Assume adds a unit clause (i.e., a clause containing one literal) containing
// just the given literal for just the next call to Solve. You can add arbitrary
// many assumptions before the next Solve. After the next call to Solve, the
// assumptions are removed.
//
// More precisely, assumptions actually remain valid even after the next call to
// Solve() returns. Valid means they remain 'assumed' until a call to
// AddClauses(), Assume(), or another Solve(), following the first Solve().
// They need to stay valid for FailedAssumptions() to return correct values.
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
	C.picosat_assume(p.p, C.int(lit))
}

// Returns non zero if the literal is a failed assumption, which is defined
// as an assumption used to derive unsatisfiability.  This is as accurate as
// generating core literals, but still of course is an overapproximation of
// the set of assumptions really necessary.  The technique does not need
// clausal core generation nor tracing to be enabled and thus can be much
// more effective.  The function can only be called as long the current
// assumptions are valid.  See Assume() for more details.
func (p *Pigosat) FailedAssumption(lit Literal) bool {
	defer p.ready(true)()
	// picoast_failed_assumption SIGABRTs if the following conditional is true
	if p.Res() != Unsatisfiable || lit == 0 {
		return false
	}
	return C.picosat_failed_assumption(p.p, C.int(lit)) != 0
}

// Returns a list of failed assumption in the last call to
// Solve(). It only makes sense if the last call to Solve()
// returned Unsatisfiable.
func (p *Pigosat) FailedAssumptions() []Literal {
	defer p.ready(true)()
	if p.Res() != Unsatisfiable {
		return nil
	}

	litPtr := C.picosat_failed_assumptions(p.p)
	return p.litArrayToSlice(litPtr)
}

// Converts a 0-terminated array of literal results to a slice.
// Does not acquire internal locks.
func (p *Pigosat) litArrayToSlice(litPtr *C.int) []Literal {
	if litPtr == nil || *litPtr == 0 {
		return []Literal{}
	}
	// It should be reasonable to use the number of vars in
	// the solver as the max array size, since we aren't tracking
	// the active number of assumptions.
	size := int(C.picosat_variables(p.p))

	var cints []C.int
	header := (*reflect.SliceHeader)(unsafe.Pointer(&cints))
	header.Cap = size
	header.Len = size
	header.Data = uintptr(unsafe.Pointer(litPtr))

	// The returned int pointer is both temporary, and larger than
	// needed, so we need to copy the real values into a new slice,
	// up until the terminator.
	ints := []Literal{}
	for _, cint := range cints {
		// break at the first sign of the 0 terminator.
		if cint == 0 {
			break
		}
		ints = append(ints, Literal(cint))
	}
	return ints
}

// Compute one maximal subset of satisfiable assumptions. You need to set
// the assumptions, call 'Solve()' before calling this function.
// The result is a list of assumptions that consistently can be asserted
// at the same time.  Before returing the library 'reassumes' all assumptions.
//
// It could be beneficial to set the default phase of assumptions
// to true (positive).  This can speed up the computation.
func (p *Pigosat) MaxSatisfiableAssumptions() []Literal {
	defer p.ready(false)()
	if C.picosat_inconsistent(p.p) != 0 {
		return []Literal{}
	}
	litPtr := C.picosat_maximal_satisfiable_subset_of_assumptions(p.p)
	return p.litArrayToSlice(litPtr)
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
// for mss := p.NextMaxSatisfiableAssumptions; len(mss) > 0; mss = p.NextMaxSatisfiableAssumptions() {
//     ProcessResults(mss)
// }
//
// can be used to iterate over all maximal consistent subsets of
// the set of assumptions {a1,a2,a3,a4}.
//
// It could be beneficial to set the default phase of assumptions
// to true (positive).  This might speed up the computation.
func (p *Pigosat) NextMaxSatisfiableAssumptions() []Literal {
	defer p.ready(false)()
	if C.picosat_inconsistent(p.p) != 0 {
		return []Literal{}
	}
	litPtr := C.picosat_next_maximal_satisfiable_subset_of_assumptions(p.p)
	return p.litArrayToSlice(litPtr)
}
