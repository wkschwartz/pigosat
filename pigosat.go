// Copyright William Schwartz 2014. See the LICENSE file for more information.

// Package pigosat is a Go binding for the PicoSAT satisfiability solver.
//
// Designing your model is beyond the scope of this document, but Googling
// "satisfiability problem", "conjunctive normal form", and "DIMACS" are good
// places to start. Once you have your model, create a Pigosat instance p with
// pigosat.NewPigosat, add the model to the instance with p.AddClauses, and
// solve with p.Solve.
package pigosat

// #cgo CFLAGS: -DNDEBUG -O3
// #cgo windows CFLAGS: -DNGETRUSAGE -DNALLSIGNALS
// #include "picosat.h" /* REMEMBER TO UPDATE func PicosatVersion BELOW! */
import "C"
import (
	"fmt"
	"os"
	"runtime"
	"sync"
	"syscall"
	"time"
	"unsafe"
)

var Version = SemanticVersion{0, 3, 1, "", 0}

// PicosatVersion returns the version string from the underlying Picosat
// library.
func PicosatVersion() string { return "960" }

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

// Struct Pigosat must be created with NewPigosat and stores the state of the
// solver. Once initialized by NewPigosat, it is safe for concurrent use.
type Pigosat struct {
	// Pointer to the underlying C struct.
	p    *C.PicoSAT
	lock *sync.RWMutex
}

// Struct Options contains optional settings for the Pigosat constructor. Zero
// values for each field indicate default behavior.
type Options struct {
	// Set PropagationLimit to a positive value to limit how long the solver
	// tries to find a solution.
	PropagationLimit uint64

	// Default (nil value) output file stdout
	OutputFile *os.File

	/* Set verbosity level. A verbosity level of 1 and above prints more and
	* more detailed progress reports on the output file, set by
	* 'picosat_set_output'. Verbose messages are prefixed with the string set
	* by 'picosat_set_prefix'.
	 */
	Verbosity uint

	// Set the prefix used for printing verbose messages and statistics.
	// Default is "c ".
	Prefix string

	/* Measure all time spent in all calls in the solver.  By default only the
	 * time spent in 'picosat_sat' is measured.  Enabling this function may for
	 * instance triple the time needed to add large CNFs, since every call to
	 * 'picosat_add' will trigger a call to 'getrusage'.
	 */
	MeasureAllCalls bool
}

// cfdopen returns a C-level FILE*. mode should be as described in fdopen(3).
func cfdopen(file *os.File, mode string) (*C.FILE, error) {
	cmode := C.CString(mode)
	defer C.free(unsafe.Pointer(cmode))
	// FILE * fdopen(int fildes, const char *mode);
	cfile, err := C.fdopen(C.int(file.Fd()), cmode)
	if err != nil {
		return nil, err
	}
	if cfile == nil {
		return nil, syscall.EINVAL
	}
	return cfile, nil
}

// NewPigosat returns a new Pigosat instance, ready to have literals added to
// it. The error return value need only be checked if the OutputFile option is
// non-nil.
func NewPigosat(options *Options) (*Pigosat, error) {
	// PicoSAT * picosat_init (void);
	p := C.picosat_init()
	if options != nil {
		// void picosat_set_propagation_limit (PicoSAT *, unsigned long long limit);
		C.picosat_set_propagation_limit(p, C.ulonglong(options.PropagationLimit))
		if options.OutputFile != nil {
			cfile, err := cfdopen(options.OutputFile, "a")
			if err != nil {
				C.picosat_reset(p)
				return nil, &os.PathError{Op: "fdopen",
					Path: options.OutputFile.Name(), Err: err}
			}
			// void picosat_set_output (PicoSAT *, FILE *);
			C.picosat_set_output(p, cfile)
		}
		// void picosat_set_verbosity (PicoSAT *, int new_verbosity_level);
		C.picosat_set_verbosity(p, C.int(options.Verbosity))
		if options.Prefix != "" {
			// void picosat_set_prefix (PicoSAT *, const char *);
			prefix := C.CString(options.Prefix)
			defer C.free(unsafe.Pointer(prefix))
			C.picosat_set_prefix(p, prefix)
		}
		if options.MeasureAllCalls {
			// void picosat_measure_all_calls (PicoSAT *);
			C.picosat_measure_all_calls(p)
		}
	}
	pgo := &Pigosat{p: p, lock: new(sync.RWMutex)}
	runtime.SetFinalizer(pgo, (*Pigosat).Delete)
	return pgo, nil
}

// Delete may be called when you are done using a Pigosat instance, after which
// it cannot be used again. However, you only need to call this method if the
// instance's finalizer was reset using runtime.SetFinalizer (if you're not
// sure, it's always safe to call Delete again). Most users will not need this
// method.
func (p *Pigosat) Delete() {
	if p == nil || p.p == nil {
		return
	}
	p.lock.Lock()
	defer p.lock.Unlock()
	// void picosat_reset (PicoSAT *);
	C.picosat_reset(p.p)
	p.p = nil
	// No longer need a finalizer. See file.close (not File.close) in the os
	// package: http://golang.org/src/pkg/os/file_unix.go#L115 (sorry if the
	// line number ends up wrong).
	runtime.SetFinalizer(p, nil)
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

// Print appends the CNF in DIMACS format to the given file.
func (p *Pigosat) Print(file *os.File) error {
	if p == nil || p.p == nil {
		return nil
	}
	p.lock.RLock()
	defer p.lock.RUnlock()
	cfile, err := cfdopen(file, "a")
	if err != nil {
		return err
	}
	// void picosat_print (PicoSAT *, FILE *);
	_, err = C.picosat_print(p.p, cfile)
	return err
}

// blocksol adds the inverse of the solution to the clauses.
// This private method does not acquire the lock or check if p is nil.
func (p *Pigosat) blocksol(sol []bool) {
	n := int(C.picosat_variables(p.p))
	for i := 1; i <= n; i++ {
		if sol[i] {
			C.picosat_add(p.p, C.int(-i))
		} else {
			C.picosat_add(p.p, C.int(i))
		}
	}
	C.picosat_add(p.p, 0)
}

// Solve the formula and return the status of the solution: one of the constants
// Unsatisfiable, Satisfiable, or Unknown. If satisfiable, return a slice
// indexed by the variables in the formula (so the first element is always
// false). Solve can be used like an iterator, yielding a new solution until
// there are no more feasible solutions:
//    for status, solution := p.Solve(); status == Satisfiable; status, solution = p.Solve() {
//        // Do stuff with status, solution
//    }
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
	p.blocksol(solution)
	return
}

// BlockSolution adds a clause to the formula ruling out a given solution. It is
// a no-op if p is nil and returns an error if the solution is the wrong
// length. There is no need to call BlockSolution after calling Pigosat.Solve,
// which calls it automatically for every Satisfiable solution.
func (p *Pigosat) BlockSolution(solution []bool) error {
	if p == nil || p.p == nil {
		return nil
	}
	p.lock.Lock()
	defer p.lock.Unlock()
	if n := int(C.picosat_variables(p.p)); len(solution) != n+1 {
		return fmt.Errorf("solution length %d, but have %d variables",
			len(solution), n)
	}
	p.blocksol(solution)
	return nil
}
