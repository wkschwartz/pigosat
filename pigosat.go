// Copyright William Schwartz 2014. See the LICENSE file for more information.

// Package pigosat is a Go binding for the PicoSAT satisfiability solver.
//
// Designing your model is beyond the scope of this document, but Googling
// "satisfiability problem", "conjunctive normal form", and "DIMACS" are good
// places to start. Once you have your model, create a Pigosat instance p with
// pigosat.New, add the model to the instance with p.AddClauses, and solve with
// p.Solve.
package pigosat

// #cgo CFLAGS: -DNDEBUG -DTRACE -O3
// #cgo windows CFLAGS: -DNGETRUSAGE -DNALLSIGNALS
// #include "picosat.h" /* REMEMBER TO UPDATE PicosatVersion BELOW! */
import "C"
import (
	"errors"
	"fmt"
	"io"
	"os"
	"runtime"
	"sync"
	"syscall"
	"time"
	"unsafe"
)

var Version = SemanticVersion{0, 4, 0, "", 0}

// PicosatVersion is the version string from the underlying Picosat library.
const PicosatVersion = "960"

// Argument/result types for Pigosat methods.

// Literals describe the variables in the formula. A positive value indicates
// the variable must be true; negative indicates it must be false. Variables
// should be indexed from one. The zero literal indicates the end of a clause.
type Literal int32

// Clauses are slices of literals ORed together. An optional zero ends a clause,
// even in the middle of a slice; [1, 0, 2] is the same as [1, 0] is the same as
// [1].
type Clause []Literal

// Formulas are slices of Clauses ANDed together.
type Formula []Clause

// Solutions are indexed by variable and return the truth value of the given
// variable. The zeroth element has no meaning and is always false.
type Solution []bool

// Statuses are returned by Pigosat.Solve to indicate success or failure.
type Status int

// Return values for Pigosat.Solve's status.
const (
	// PicoSAT cannot determine the satisfiability of the formula.
	Unknown Status = C.PICOSAT_UNKNOWN
	// The formula is satisfiable.
	Satisfiable Status = C.PICOSAT_SATISFIABLE
	// The formula cannot be satisfied.
	Unsatisfiable Status = C.PICOSAT_UNSATISFIABLE
)

// Struct Pigosat must be created with New and stores the state of the
// solver. It is safe for concurrent use.
//
// You must not use runtime.SetFinalizer with Pigosat objects. Attempting to
// call a method on an uninitialized Pigosat object panics.
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

	// If you want to extract cores or proof traces using WriteClausalCore,
	// WriteCompactTrace, WriteExtendedTrace with the current instance of
	// Pigosat, then set this option true. This option may increase memory
	// usage.
	EnableTrace bool
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

// New returns a new Pigosat instance, ready to have literals added to it. The
// error return value need only be checked if the OutputFile option is non-nil.
func New(options *Options) (*Pigosat, error) {
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
		if options.EnableTrace {
			if int(C.picosat_enable_trace_generation(p)) == 0 {
				// The cgo CFLAGS guarantee trace generation using -DTRACE.
				panic("trace generation was not enabled in build")
			}
		}
	}
	pgo := &Pigosat{p: p, lock: new(sync.RWMutex)}
	runtime.SetFinalizer(pgo, (*Pigosat).delete)
	return pgo, nil
}

// delete frees memory associated with p's PicoSAT object. It only needs to be
// called from the runtime.SetFinalizer set in New.
func (p *Pigosat) delete() {
	// For some reason, SetFinalizer needs delete to be idempotent/reentrant.
	// That said, since finalizers are only run when there are no more
	// references to the object, there doesn't seem to be any point in locking.
	if p.p == nil {
		return
	}
	// void picosat_reset (PicoSAT *);
	C.picosat_reset(p.p)
	p.p = nil
}

// ready readies a Pigosat object for use in a public method. It obtains the
// appropriate lock and returns the appropriate unlocking method, so it can be
// used like
//     defer p.ready(readonly)()
// where readonly should be true if the method does not write to p and must be
// false if the method does write to p. If p is uninitialized or deleted,
// ready panics.
func (p *Pigosat) ready(readonly bool) (unlock func()) {
	if readonly {
		p.lock.RLock()
		unlock = p.lock.RUnlock
	} else {
		p.lock.Lock()
		unlock = p.lock.Unlock
	}
	if p.p == nil {
		defer unlock()
		panic("Attempted to use a deleted Pigosat object")
	}
	return
}

// Variables returns the number of variables in the formula: The m in the DIMACS
// header "p cnf <m> n".
func (p *Pigosat) Variables() int {
	defer p.ready(true)()
	// int picosat_variables (PicoSAT *);
	return int(C.picosat_variables(p.p))
}

// AddedOriginalClauses returns the number of clauses in the formula: The n in
// the DIMACS header "p cnf m <n>".
func (p *Pigosat) AddedOriginalClauses() int {
	defer p.ready(true)()
	// int picosat_added_original_clauses (PicoSAT *);
	return int(C.picosat_added_original_clauses(p.p))
}

// Seconds returns the time spent in the PicoSAT library.
func (p *Pigosat) Seconds() time.Duration {
	defer p.ready(true)()
	// double picosat_seconds (PicoSAT *);
	return time.Duration(float64(C.picosat_seconds(p.p)) * float64(time.Second))
}

// AddClauses adds a slice of clauses, each of which are a slice of literals.
// Each clause is a list of integers called literals. The absolute value of the
// literal i is the subscript for some variable x_i. If the literal is positive,
// x_i must end up being true when the formula is solved. If the literal is
// negative, it must end up false. Each clause ORs the literals together. All
// the clauses are ANDed together. An optional zero ends a clause, even in the
// middle of a slice; [1, 0, 2] is the same as [1, 0] is the same as [1].
func (p *Pigosat) AddClauses(clauses Formula) {
	defer p.ready(false)()
	var count int
	for _, clause := range clauses {
		count = len(clause)
		if count == 0 {
			continue
		}
		if clause[count-1] != 0 { // 0 tells PicoSAT where to stop reading array
			clause = append(clause, 0)
		}
		// int picosat_add_lits (PicoSAT *, int * lits);
		C.picosat_add_lits(p.p, (*C.int)(&clause[0]))
	}
}

// Print appends the CNF in DIMACS format to the given file.
func (p *Pigosat) Print(w io.Writer) error {
	defer p.ready(true)()
	return cFileWriterWrapper(w, func(cfile *C.FILE) error {
		// void picosat_print (PicoSAT *, FILE *);
		_, err := C.picosat_print(p.p, cfile)
		return err
	})
}

// blocksol adds the inverse of the solution to the clauses.
// This private method does not acquire the lock or check if p is nil.
func (p *Pigosat) blocksol(sol Solution) {
	n := C.picosat_variables(p.p)
	clause := make([]C.int, n+1)
	for i := C.int(1); i <= n; i++ {
		if sol[i] {
			clause[i-1] = -i
		} else {
			clause[i-1] = i
		}
	}
	// int picosat_add_lits (PicoSAT *, int * lits);
	C.picosat_add_lits(p.p, &clause[0])
}

// Solve the formula and return the status of the solution: one of the constants
// Unsatisfiable, Satisfiable, or Unknown. If satisfiable, return a slice
// indexed by the variables in the formula (so the first element is always
// false). Solve can be used like an iterator, yielding a new solution until
// there are no more feasible solutions:
//    for status, solution := p.Solve(); status == Satisfiable; status, solution = p.Solve() {
//        // Do stuff with status, solution
//    }
func (p *Pigosat) Solve() (status Status, solution Solution) {
	defer p.ready(false)()
	// int picosat_sat (PicoSAT *, int decision_limit);
	status = Status(C.picosat_sat(p.p, -1))
	if status == Unsatisfiable || status == Unknown {
		return
	} else if status != Satisfiable {
		panic(fmt.Errorf("Unknown sat status: %d", status))
	}
	n := int(C.picosat_variables(p.p)) // Calling Pigosat.Variables deadlocks
	solution = make(Solution, n+1)
	for i := 1; i <= n; i++ {
		// int picosat_deref (PicoSAT *, int lit);
		if val := C.picosat_deref(p.p, C.int(i)); val > 0 {
			solution[i] = true
		} else if val == 0 {
			panic(fmt.Errorf("Variable %d was assigned value 0", i))
		}
	}
	p.blocksol(solution)
	return
}

// Res returns Solve's last status, or Unknown if Solve hasn't yet been called.
func (p *Pigosat) Res() (status Status) {
	defer p.ready(true)()
	// int picosat_res (PicoSAT *);
	return Status(C.picosat_res(p.p))
}

// BlockSolution adds a clause to the formula ruling out a given solution. It is
// a no-op if p is nil and returns an error if the solution is the wrong
// length. There is no need to call BlockSolution after calling Pigosat.Solve,
// which calls it automatically for every Satisfiable solution.
func (p *Pigosat) BlockSolution(solution Solution) error {
	defer p.ready(false)()
	if n := int(C.picosat_variables(p.p)); len(solution) != n+1 {
		return fmt.Errorf("solution length %d, but have %d variables",
			len(solution), n)
	}
	p.blocksol(solution)
	return nil
}

// Write the clauses that were used in deriving the empty clause to a file
// in DIMACS format.
//
// Requires that Pigosat was created with EnableTrace == true.
func (p *Pigosat) WriteClausalCore(f io.Writer) error {
	defer p.ready(true)()
	if Status(C.picosat_res(p.p)) != Unsatisfiable {
		return errors.New("expected to be in Unsatisfiable state")
	}

	return cFileWriterWrapper(f, func(cfile *C.FILE) error {
		// void picosat_write_clausal_core (PicoSAT *, FILE * core_file);
		_, err := C.picosat_write_clausal_core(p.p, cfile)
		return err
	})
}

// Write a compact proof trace in TraceCheck format to a file.
//
// Requires that Pigosat was created with EnableTrace == true.
func (p *Pigosat) WriteCompactTrace(f io.Writer) error {
	defer p.ready(true)()
	if Status(C.picosat_res(p.p)) != Unsatisfiable {
		return errors.New("expected to be in Unsatisfiable state")
	}

	return cFileWriterWrapper(f, func(cfile *C.FILE) error {
		// void picosat_write_compact_trace (PicoSAT *, FILE * trace_file);
		_, err := C.picosat_write_compact_trace(p.p, cfile)
		return err
	})
}

// Write an extended proof trace in TraceCheck format to a file.
//
// Requires that Pigosat was created with EnableTrace == true.
func (p *Pigosat) WriteExtendedTrace(f io.Writer) error {
	defer p.ready(true)()
	if Status(C.picosat_res(p.p)) != Unsatisfiable {
		return errors.New("expected to be in Unsatisfiable state")
	}

	return cFileWriterWrapper(f, func(cfile *C.FILE) error {
		// void picosat_write_extended_trace (PicoSAT *, FILE * trace_file);
		_, err := C.picosat_write_extended_trace(p.p, cfile)
		return err
	})
}

// A wrapper to take an io.Writer interface and feed it
// the output from picosat functions that specifically
// need a *C.FILE
func cFileWriterWrapper(w io.Writer, writeFn func(*C.FILE) error) (err error) {
	rp, wp, err := os.Pipe()
	if err != nil {
		return err
	}
	// Don't hide prior errors if the pipe closes without errors.
	close = func (closer io.Closer) {
			if e := closer.Close(); e != nil {
				err = e
			}
		}
	defer close(wp)
	defer close(rp)

	cfile, err := cfdopen(wp, "a")
	if err != nil {
		return err
	}
	defer func () {
			if _, e := C.fclose(cfile); e != nil {
				err = e
			}
		}()

	err = writeFn(cfile)
	if err != nil {
		return err
	}
	_, err = io.Copy(w, rp)
	return err
}
