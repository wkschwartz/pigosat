// Copyright William Schwartz 2014. All rights reserved.

// Package pigosat is a Go binding for the PicoSAT satisfiability solver.
package pigosat

// #include "picosat/picosat.h"
import "C"

// Note: Any comment that is in the /**/ style is (at least mostly) copied
// directly from version 957 of picosat.h.

// Return values for Picosat.Solve's status.
const (
	// NotReady is a solver status only used in PiGoSAT and it means the
	// underlying data structures of the solver have not been initialized or
	// their memory was previously freed.
	NotReady = -1
	// PicoSAT cannot determine the satisfiability of the formula.
	UNKNOWN = 0
	// The formula is satisfiable.
	SATISFIABLE = 10
	// The formula cannot be satisfied.
	UNSATISFIABLE = 20
)

// Struct Picosat must be created with NewPicosat and destroyed with DelPicosat.
type Picosat struct {
	// Pointer to the underlying C struct.
	p *C.PicoSAT
}

// NewPicosat returns a new Picosat instance, ready to have literals added to
// it.
func NewPicosat() Picosat {
	// PicoSAT * picosat_init (void);
	return &Picosat{p: C.picosat_init()}
}

// DelPicosat must be called on every Picosat instance before each goes out of
// scope or the program ends, or else the program will leak memory. Once
// DelPicosat has been called on an instance, it cannot be used again.
func (p *Picosat) DelPicosat() {
	if p == nil || p.p == nil {
		return
	}
	// void picosat_reset (PicoSAT *);
	C.picosat_reset(p.p)
	p.p = nil
}

/* SetSeed: Set a seed for the random number generator. The random number generator
 * is currently just used for generating random decisions.  In our
 * experiments having random decisions did not really help on industrial
 * examples, but was rather helpful to randomize the solver in order to
 * do proper benchmarking of different internal parameter sets.
 */
func (p *Picosat) SetSeed(seed uint32) {
	if p == nil || p.p == nil {
		return
	}
	// void picosat_set_seed (PicoSAT *, unsigned random_number_generator_seed);
	C.picosat_set_seed(p.p, C.uint(seed))
}

// Variables returns the number of variables in the formula: The m in the DIMACS
// header "p cnf <m> n".
func (p *Picosat) Variables() int {
	if p == nil || p.p == nil {
		return 0
	}
	// int picosat_variables (PicoSAT *);
	return C.picosat_variables(p.p)
}

// AddedOriginalClauses returns the number of clauses in the formula: The n in
// the DIMACS header "p cnf m <n>".
func (p *Picosat) AddedOriginalClauses() int {
	if p == nil || p.p == nil {
		return 0
	}
	// int picosat_added_original_clauses (PicoSAT *);
	return C.picosat_added_original_clauses(p.p)
}

// Seconds returns the time spent in the PicoSAT library.
func (p *Picosat) Seconds() time.Duration {
	if p == nil || p.p == nil {
		return 0
	}
	// double picosat_seconds (PicoSAT *);
	return time.Duration(C.picosat_seconds(p.p) * time.Second)
}

// AddLits adds the next clause, resetting the solver if Solve had been called
// already. Including a zero in the clause terminates the clause (thus allowing
// you to use one slice as reusable buffer). Otherwise the clause ends at the
// end of the slice.
func (p *Picosat) AddClause(clause []int32) {
	if p == nil || p.p == nil {
		return
	}
	c := make([]C.int, len(clause))
	var had0 bool
	for i, v := range clause {
		c[i] = C.int(v)
		if v == 0 {
			had0 = true
			break
		}
	}
	if !had0 {
		c = append(c, 0)
	}
	// int picosat_add_lits (PicoSAT *, int * lits);
	C.picosat_add_lits(p.p, &c[0])
}

// Solve the formula and return the status of the solution: one of the constants
// UNSATISFIABLE, SATISFIABLE, or UNKNOWN. If satisfiable, return a slice
// indexed by the variables in the formula (so the first element is always
// zero). A negative decision limit sets no limit on the number of decisions.
func (p *Picosat) Solve(decision_limit int) (status int, solution []bool) {
	if p == nil || p.p == nil {
		return NotReady, nil
	}
	// int picosat_sat (PicoSAT *, int decision_limit);
	status = C.picosat_sat(p.p, C.int(decision_limit))
	if status == UNSATISFIABLE || status == UNKNOWN {
		return
	} else if status != SATISFIABLE {
		panic(fmt.Errorf("Unknown sat status: %d", status))
	}
	n := p.Variables()
	solution = make([]bool, n)
	for i := 1; i <= n; i++ {
		// int picosat_deref (PicoSAT *, int lit);
		if val := C.picosat_deref(p.p, C.int(lit)); val > 0 {
			solution[i] = true
		} else if val < 0 {
			solution[i] = false
		} else {
			panic(fmt.Errof("Variable %d was assigned value 0", i))
		}
	}
}
