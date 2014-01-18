// Copyright William Schwartz 2014. See the LICENSE file for more information.

// Package pigosat is a Go binding for the PicoSAT satisfiability solver.
package pigosat

// picosat/libpicosat.a must exist to build this file. See README.md.

// #cgo CFLAGS: -I picosat
// #cgo LDFLAGS: -l picosat -L picosat
// #include "picosat.h"
import "C"
import "time"
import "fmt"
import "sync"

var Version = SemanticVersion{0, 1, 0, "", 0}

// PicosatVersion returns the version string from the underlying Picosat
// library.
func PicosatVersion() string {
	return C.GoString(C.picosat_version())
}

// Return values for Pigosat.Solve's status.
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

// Struct Pigosat must be created with NewPigosat and destroyed with DelPigosat.
type Pigosat struct {
	// Pointer to the underlying C struct.
	p *C.PicoSAT
	lock *sync.RWMutex
}

// NewPigosat returns a new Pigosat instance, ready to have literals added to
// it. Set propogation_limit to a positive value to limit how long the solver
// tries to find a solution.
func NewPigosat(propagation_limit uint64) *Pigosat {
	// PicoSAT * picosat_init (void);
	p := C.picosat_init()
	// void picosat_set_propagation_limit (PicoSAT *, unsigned long long limit);
	// Must be called after init, before solve, so we do it in the constructor.
	if propagation_limit > 0 {
		C.picosat_set_propagation_limit(p, C.ulonglong(propagation_limit))
	}
	return &Pigosat{p: p, lock: new(sync.RWMutex)}
}

// DelPigosat must be called on every Pigosat instance before each goes out of
// scope or the program ends, or else the program will leak memory. Once
// DelPigosat has been called on an instance, it cannot be used again.
func (p *Pigosat) Delete() {
	if p == nil || p.p == nil {
		return
	}
	p.lock.Lock()
	defer p.lock.Unlock()
	// void picosat_reset (PicoSAT *);
	C.picosat_reset(p.p)
	p.p = nil
}

// Variables returns the number of variables in the formula: The m in the DIMACS
// header "p cnf <m> n".
func (p *Pigosat) Variables() int {
	if p == nil || p.p == nil {
		return 0
	}
	p.lock.RLock()
	defer p.lock.RUnlock()
	// int picosat_variables (PicoSAT *);
	return int(C.picosat_variables(p.p))
}

// AddedOriginalClauses returns the number of clauses in the formula: The n in
// the DIMACS header "p cnf m <n>".
func (p *Pigosat) AddedOriginalClauses() int {
	if p == nil || p.p == nil {
		return 0
	}
	p.lock.RLock()
	defer p.lock.RUnlock()
	// int picosat_added_original_clauses (PicoSAT *);
	return int(C.picosat_added_original_clauses(p.p))
}

// Seconds returns the time spent in the PicoSAT library.
func (p *Pigosat) Seconds() time.Duration {
	if p == nil || p.p == nil {
		return 0
	}
	p.lock.RLock()
	defer p.lock.RUnlock()
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
func (p *Pigosat) AddClauses(clauses [][]int32) {
	if p == nil || p.p == nil {
		return
	}
	p.lock.Lock()
	defer p.lock.Unlock()
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
func (p *Pigosat) Solve() (status int, solution []bool) {
	if p == nil || p.p == nil {
		return NotReady, nil
	}
	p.lock.Lock()
	defer p.lock.Unlock()
	// int picosat_sat (PicoSAT *, int decision_limit);
	status = int(C.picosat_sat(p.p, -1))
	if status == Unsatisfiable || status == Unknown {
		return
	} else if status != Satisfiable {
		panic(fmt.Errorf("Unknown sat status: %d", status))
	}
	n := int(C.picosat_variables(p.p)) // Calling Pigosat.Variables deadlocks
	solution = make([]bool, n+1)
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
