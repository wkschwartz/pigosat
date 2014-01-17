// Copyright William Schwartz 2014. All rights reserved.

// Package pigosat is a Go binding for the PicoSAT satisfiability solver.
package pigosat

// To build the PicoSAT dependency, run
//     $ cd picosat; make picosat.o
// No need to run picosat/configure.

// #cgo CFLAGS:-I picosat
// #cgo LDFLAGS: -l picosat.o -L picosat
// #include "picosat.h"
import "C"
import "time"
import "fmt"

// Note: Any comment that is in the /**/ style is (at least mostly) copied
// directly from version 957 of picosat.h.

// Return values for Picosat.Solve's status.
const (
	// NotReady is a solver status only used in PiGoSAT and it means the
	// underlying data structures of the solver have not been initialized or
	// their memory was previously freed.
	NotReady = -1
	// PicoSAT cannot determine the satisfiability of the formula.
	Unknown = 0
	// The formula is satisfiable.
	Satisfiable = 10
	// The formula cannot be satisfied.
	Unsatisfiable = 20
)

// Struct Picosat must be created with NewPicosat and destroyed with DelPicosat.
type Picosat struct {
	// Pointer to the underlying C struct.
	p *C.PicoSAT
}

// NewPicosat returns a new Picosat instance, ready to have literals added to
// it. Set propogation_limit to a positive value to limit how long the solver
// tries to find a solution.
func NewPicosat(propagation_limit uint64) *Picosat {
	// PicoSAT * picosat_init (void);
	p := C.picosat_init()
	// void picosat_set_propagation_limit (PicoSAT *, unsigned long long limit);
	// Must be called after init, before solve, so we do it in the constructor.
	if propagation_limit > 0 {
		C.picosat_set_propagation_limit(p, C.ulonglong(propagation_limit))
	}
	return &Picosat{p: p}
}

// DelPicosat must be called on every Picosat instance before each goes out of
// scope or the program ends, or else the program will leak memory. Once
// DelPicosat has been called on an instance, it cannot be used again.
func (p *Picosat) Delete() {
	if p == nil || p.p == nil {
		return
	}
	// void picosat_reset (PicoSAT *);
	C.picosat_reset(p.p)
	p.p = nil
}

// Variables returns the number of variables in the formula: The m in the DIMACS
// header "p cnf <m> n".
func (p *Picosat) Variables() int {
	if p == nil || p.p == nil {
		return 0
	}
	// int picosat_variables (PicoSAT *);
	return int(C.picosat_variables(p.p))
}

// AddedOriginalClauses returns the number of clauses in the formula: The n in
// the DIMACS header "p cnf m <n>".
func (p *Picosat) AddedOriginalClauses() int {
	if p == nil || p.p == nil {
		return 0
	}
	// int picosat_added_original_clauses (PicoSAT *);
	return int(C.picosat_added_original_clauses(p.p))
}

// Seconds returns the time spent in the PicoSAT library.
func (p *Picosat) Seconds() time.Duration {
	if p == nil || p.p == nil {
		return 0
	}
	// double picosat_seconds (PicoSAT *);
	return time.Duration(float64(C.picosat_seconds(p.p)) * float64(time.Second))
}

// AddClauses adds a list (as a slice) of clauses (the sub-slices). Each clause
// is a list of integers called literals. The absolute value of the literal i is
// the subscript for some variable x_i. If the literal is positive, x_i must end
// up being true when the formula is solved. If the literal is negative, it must
// end up false. Each clause ORs the literals together. All the clauses are
// ANDed together. Literals cannot be zero: a zero in the middle of a slice ends
// the clause, and causes AddClauses to skip reading the rest of the slice. Nil
// slices are ignored and skipped.
func (p *Picosat) AddClauses(clauses [][]int32) {
	if p == nil || p.p == nil {
		return
	}
	var had0 bool
	for _, clause := range clauses {
		if len(clause) == 0 {
			continue
		}
		had0 = false
		for _, lit := range clause {
			// int picosat_add (PicoSAT *, int lit);
			C.picosat_add(p.p, C.int(lit))
			if lit == 0 {
				had0 = true
				break
			}
		}
		if !had0 {
			C.picosat_add(p.p, 0)
		}
	}
}

// Solve the formula and return the status of the solution: one of the constants
// Unsatisfiable, Satisfiable, or Unknown. If satisfiable, return a slice
// indexed by the variables in the formula (so the first element is always
// false).
func (p *Picosat) Solve() (status int, solution []bool) {
	if p == nil || p.p == nil {
		return NotReady, nil
	}
	// int picosat_sat (PicoSAT *, int decision_limit);
	status = int(C.picosat_sat(p.p, -1))
	if status == Unsatisfiable || status == Unknown {
		return
	} else if status != Satisfiable {
		panic(fmt.Errorf("Unknown sat status: %d", status))
	}
	n := p.Variables()
	solution = make([]bool, n + 1)
	for i := 1; i <= n; i++ {
		// int picosat_deref (PicoSAT *, int lit);
		if val := C.picosat_deref(p.p, C.int(i)); val > 0 {
			solution[i] = true
		} else if val < 0 {
			solution[i] = false
		} else {
			panic(fmt.Errorf("Variable %d was assigned value 0", i))
		}
	}
	return
}
