// Copyright William Schwartz 2014. See the LICENSE file for more information.

// Package pigosat is a Go binding for the PicoSAT satisfiability solver.
//
// A satisfiability (SAT) solver is for solving expressions such as
//     (a || b || !c) && (c || !d)
// for logical variables a, b, c, and d so that the expression is true. The
// whole expression is called a formula and each parenthesized unit is called a
// clause. Variables such as c and their negations such as !c are called
// literals. The SAT formulation PicoSAT, and thereby PiGoSAT, uses is called
// "conjunctive normal form" (CNF) dictates that formulas are the conjunctions
// (AND) of clauses, and clauses are the disjunction (OR) of literals. To allow
// arbitrary numbers of literals, we think of variables as having names like
// x_k, where k is an integer at least 1. Empty clauses evaluate to false.
//
// In PicoSAT, and thereby PiGoSAT, we refer to variable x_k simply as k.
// Instead of a NOT operator ! as part of negated literals, we take the additive
// inverse, so -k instead of !x_k. Zero is never the name of a variable, so we
// can use it to mark the end of clauses. In PiGoSAT, the Literal type is an
// integer type, the Clause type is a slice of Literals, and the Formula type is
// a slice of Clauses. Thus, the formula above might be written as
//     Formula{Clause{1, 2, -3, 0}, Clause{3, 4, 0}}
// A solution to this formula assigns truth values to variables x_1, ..., x_4.
// Using the Solution type, we could write a solution to the above formula as
//     Solution{1: true, 2: false, 3: false, 4: false}
// (Notice that the zeroth element is always false). This works because we can
// substitute for the variables as follows
//     (true || false || !false) && (false || !false)
// which evaluates to true. There are many solutions to the formula. Another one
// is
//     Solution{1: false, 2: true, 3: false, 4: false}
//
// Use the Pigosat type to solve SAT problems as follows. First create a Pigosat
// instance:
//     p := New(nil).
// The argument to New allows advanced users to pass in an Option instance. See
// its documentation for details. Next, supply the Pigosat instance with your
// formula:
//     p.Add(Formula{{1, 2, -3}, {3, 4}})
// (This is also a correct way to write the formula for PiGoSAT.)
//
// Calling p.Solve() returns two objects. The second is a Status object, one of
// the constants Satisfiable, Unsatisfiable, or Unknown. The latter is the
// status when some (optional) limitation prevents Solve from working long
// enough to find a solution. This is important because p.Solve() has time
// complexity exponential in the size of the formula in the worst case, meaning
// p.Solve() can be very slow. Hopefully you will get a status of Satisfiable or
// Unsatisfiable. If the status is Unsatisfiable or Unknown, the solution will
// be nil. If the status is Satisfiable, the first return value is a Solution
// object, such as one of the ones above. The Solution object is a proof of
// satisfiability in the Satisfiable case.
//
// p.Solve() can just tell you yes or no to a formula, but PiGoSAT has
// facilities for optimization problems as well. Check out the Minimizer
// interface and the Minimize function. The idea is that Minimize calls a
// function you write called IsFeasible with different integer parameter values.
// IsFeasible generates a formula based on this parameter, constructs a Pigosat
// object, and calls its Solve method. If your problem is such that IsFeasible
// always returns Satisfiable above some parameter value K and Unsatisfiable
// below K, Minimize can find K. An example of where this is useful is in graph
// coloring problems. The parameter can represent the number of available
// colors. Your custom IsFeasible function generates a formula based on some
// input graph to determine whether there is a proper coloring (an assignment
// of colors to vertices so that neighboring vertices have different colors) of
// the graph that uses at most that number of colors. Minimize can then
// determine the chromatic number of the graph, the minimum number of colors
// needed for a proper coloring.
package pigosat

// #cgo CFLAGS: -DNDEBUG -DTRACE -O3
// #cgo windows CFLAGS: -DNGETRUSAGE -DNALLSIGNALS
// #include "picosat.h" /* REMEMBER TO UPDATE PicosatVersion BELOW! */
import "C"
import (
	"bytes"
	"fmt"
	"io"
	"os"
	"runtime"
	"sync"
	"syscall"
	"time"
	"unsafe"
)

// Version is PiGoSAT's semantic version number. See http://semver.org.
const Version = "1.0.1"

// PicosatVersion is the version string from the underlying PicoSAT library.
const PicosatVersion = "965"

// Argument/result types for Pigosat methods.

// Literal represents a variable or its logical negations. We name variables by
// ID numbers starting from one and use arithmetic negation to indicate logical
// negation. The zero literal indicates the end of a clause.
type Literal int32

// Clause is a slice of Literals ORed together. An optional zero ends a clause,
// even in the middle of a slice: [1, 0, 2] is the same as [1, 0] is the same as
// [1]. An empty Clause always evaluates false and thus can never be satisfied.
type Clause []Literal

// Formula is a slice of Clauses ANDed together.
type Formula []Clause

// Solution is a slice of truth values indexed by and corresponding to each
// variable's ID number (starting at one). The zeroth element has no meaning and
// is always false.
type Solution []bool

// String returns a readable string like "{1:true, 2:false, ...}" for Solution
// s.
func (s Solution) String() string {
	var buffer bytes.Buffer
	buffer.WriteString("{")
	if len(s) <= 1 {
		buffer.WriteString("}")
	} else {
		for variable, value := range s[1 : len(s)-1] {
			buffer.WriteString(fmt.Sprintf("%d:%-5v, ", variable+1, value))
		}
		buffer.WriteString(fmt.Sprintf("%d:%v}", len(s)-1, s[len(s)-1]))
	}
	return buffer.String()
}

// Status is returned by Pigosat.Solve to indicate success or failure.
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

// For use in Status.String.
var statusNames = map[Status]string{Unknown: "Unknown",
	Satisfiable: "Satisfiable", Unsatisfiable: "Unsatisfiable"}

// String returns a readable string such as "Satisfiable" from Status s.
func (s Status) String() string {
	if name, ok := statusNames[s]; ok {
		return name
	}
	return fmt.Sprintf("Status(%d)", s)
}

// Pigosat must be created with New and stores the state of the solver. It is
// safe for concurrent use.
//
// You must not use runtime.SetFinalizer with Pigosat objects. Attempting to
// call a method on an uninitialized or deleted Pigosat object panics.
//
// Casual users of PiGoSAT need not call the Delete method. More intensive users
// should consult Delete's documentation.
type Pigosat struct {
	// Pointer to the underlying C struct.
	p    *C.PicoSAT
	lock sync.RWMutex
	// This allows us to avoid the crash demonstrated in
	// TestCrashOnUnsatResetFailedAssumptions. We keep it set to false except
	// when Solve just returned Unsatisfiable and nothing has happened to render
	// assumptions invalid (see documentation for Assume). We reset it to false
	// every time assumptions become invalid.
	couldHaveFailedAssumptions bool
}

// Options contains optional settings for the Pigosat constructor. Zero values
// for each field indicate default behavior.
type Options struct {
	// Set PropagationLimit to a positive value to limit how long the solver
	// tries to find a solution.
	PropagationLimit uint64

	// Default (nil value) output file is standard out. The client is
	// responsible for closing the file after he is done with the Pigosat
	// object.
	OutputFile *os.File

	// Set verbosity level. A verbosity level of 1 and above prints more and
	// more detailed progress reports on the output file, set by OutputFile.
	// Verbose messages are prefixed with the string set by Prefix.
	Verbosity uint

	// Set the prefix used for printing verbose messages and statistics.
	// Default is "c ".
	Prefix string

	// Measure all time spent in all calls in PicoSAT's solver (extra time in
	// PiGoSAT is generally linear in the number of variables). By default only
	// the time spent in PicoSAT's internal solver is measured. Setting this
	// option may as much as triple the time needed to add large formulas.
	MeasureAllCalls bool

	// If you want to extract cores or proof traces using WriteClausalCore,
	// WriteCompactTrace, WriteExtendedTrace, then set this option true. Doing
	// so may increase memory usage.
	EnableTrace bool
}

// cfdopen returns a C-level FILE*. mode should be as described in fdopen(3).
func cfdopen(file *os.File, mode string) (*C.FILE, error) {
	cmode := C.CString(mode)
	defer C.free(unsafe.Pointer(cmode))
	// FILE * fdopen(int fildes, const char *mode);
	cfile, err := C.fdopen(C.int(file.Fd()), cmode)
	// Sometimes err != nil even after successful call because fdopen caught an
	// error but didn't clear errno. See
	// http://comp.unix.programmer.narkive.com/g4gxgYP4/fdopen-cause-illegal-seek
	if cfile == nil {
		if err == nil {
			err = syscall.EINVAL
		}
		return nil, err
	}
	return cfile, nil
}

// New returns a new Pigosat instance, ready to have literals added to it. The
// error return value need only be checked if the OutputFile option is non-nil.
// If options is nil, New chooses all defaults.
func New(options *Options) (*Pigosat, error) {
	// PicoSAT * picosat_init (void);
	p := C.picosat_init()
	if options != nil {
		if options.PropagationLimit > 0 {
			// void picosat_set_propagation_limit (PicoSAT *, unsigned long long limit);
			C.picosat_set_propagation_limit(p, C.ulonglong(options.PropagationLimit))
		}
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
		if options.Verbosity > 0 {
			// void picosat_set_verbosity (PicoSAT *, int new_verbosity_level);
			C.picosat_set_verbosity(p, C.int(options.Verbosity))
		}
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
	pgo := &Pigosat{p: p, lock: sync.RWMutex{}}
	runtime.SetFinalizer(pgo, (*Pigosat).Delete)
	return pgo, nil
}

// Delete frees memory associated with p's PicoSAT object. Use of p's methods
// after calling p.Delete() panics.
//
// Casual users do not need to call p.Delete() explicitly. The Go garbage
// collector should call it automatically as a finalizer. However, if you are
// creating large numbers of Pigosat objects or are writing a library,
// explicitly call p.Delete() because the Go garbage collector does not
// guarantee when or whether finalizers run.
func (p *Pigosat) Delete() {
	defer p.ready(false)() // Do not zero-out p.lock.
	if p.p == nil {
		return
	}
	// void picosat_reset (PicoSAT *);
	C.picosat_reset(p.p)
	p.p = nil
	runtime.SetFinalizer(p, nil)
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

// Add appends a slice of Clauses to p's existing formula. See the documentation
// for Literal, Clause, and Formula to understand how p.Solve will interpret the
// formula.
//
// A zero in a clause terminates the clause even if the zero is not at the end
// of the slice. An empty clause always causes the formula to be unsatisfiable.
func (p *Pigosat) Add(clauses Formula) {
	defer p.ready(false)()
	var count int
	for _, clause := range clauses {
		p.couldHaveFailedAssumptions = false
		count = len(clause)
		if count == 0 {
			// int picosat_add (PicoSAT *, int lit);
			C.picosat_add(p.p, 0)
			continue
		}
		if clause[count-1] != 0 { // 0 tells PicoSAT where to stop reading array
			clause = append(clause, 0)
		}
		// int picosat_add_lits (PicoSAT *, int * lits);
		C.picosat_add_lits(p.p, (*C.int)(&clause[0]))
	}
}

// Print appends the formula in DIMACS format to the given io.Writer.
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
	p.couldHaveFailedAssumptions = false
	// int picosat_add_lits (PicoSAT *, int * lits);
	C.picosat_add_lits(p.p, &clause[0])
}

// Solve the formula and return the status of the solution: one of the constants
// Unsatisfiable, Satisfiable, or Unknown. If satisfiable, return a slice
// indexed by the variables in the formula (so the first element is always
// false). Assigning these boolean values to the variables will satisfy the
// formula and assumptions that p.Add and p.Assume have added to the Pigosat
// object. See the documentation for Assume regarding when assumptions are
// valid.
//
// Solve can be used like an iterator, yielding a new solution until there are
// no more feasible solutions:
//    for solution, status := p.Solve(); status == Satisfiable; solution, status = p.Solve() {
//        // Do stuff with solution, status
//        p.BlockSolution(solution)
//    }
func (p *Pigosat) Solve() (solution Solution, status Status) {
	defer p.ready(false)()
	p.couldHaveFailedAssumptions = false
	// int picosat_sat (PicoSAT *, int decision_limit);
	status = Status(C.picosat_sat(p.p, -1))
	if status == Unsatisfiable {
		p.couldHaveFailedAssumptions = true
		return
	} else if status == Unknown {
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
	return
}

// Res returns Solve's last status, or Unknown if Solve hasn't yet been called.
func (p *Pigosat) Res() (status Status) {
	defer p.ready(true)()
	return p.res()
}

// res returns Solve's last status, or Unknown if Solve hasn't yet been called.
// res does not lock, whereas Res locks.
func (p *Pigosat) res() (status Status) {
	// int picosat_res (PicoSAT *);
	return Status(C.picosat_res(p.p))
}

// BlockSolution adds a clause to the formula ruling out a given solution. It
// returns an error if the solution is the wrong length.
func (p *Pigosat) BlockSolution(solution Solution) error {
	defer p.ready(false)()
	if n := int(C.picosat_variables(p.p)); len(solution) != n+1 {
		return fmt.Errorf("solution length %d, but have %d variables",
			len(solution), n)
	}
	p.blocksol(solution)
	return nil
}

// WriteClausalCore writes in DIMACS format the clauses that were used in
// deriving the empty clause. Requires that p was created with EnableTrace.
func (p *Pigosat) WriteClausalCore(f io.Writer) error {
	defer p.ready(true)()
	if Status(C.picosat_res(p.p)) != Unsatisfiable {
		return fmt.Errorf("expected to be in Unsatisfiable state")
	}

	return cFileWriterWrapper(f, func(cfile *C.FILE) error {
		// void picosat_write_clausal_core (PicoSAT *, FILE * core_file);
		_, err := C.picosat_write_clausal_core(p.p, cfile)
		return err
	})
}

// WriteCompactTrace writes a compact proof trace in TraceCheck format. Requires
// that p was created with EnableTrace.
func (p *Pigosat) WriteCompactTrace(f io.Writer) error {
	defer p.ready(true)()
	if Status(C.picosat_res(p.p)) != Unsatisfiable {
		return fmt.Errorf("expected to be in Unsatisfiable state")
	}

	return cFileWriterWrapper(f, func(cfile *C.FILE) error {
		// void picosat_write_compact_trace (PicoSAT *, FILE * trace_file);
		_, err := C.picosat_write_compact_trace(p.p, cfile)
		return err
	})
}

// WriteExtendedTrace writes an extended proof trace in TraceCheck format.
// Requires that p was created with EnableTrace.
func (p *Pigosat) WriteExtendedTrace(f io.Writer) error {
	defer p.ready(true)()
	if Status(C.picosat_res(p.p)) != Unsatisfiable {
		return fmt.Errorf("expected to be in Unsatisfiable state")
	}

	return cFileWriterWrapper(f, func(cfile *C.FILE) error {
		// void picosat_write_extended_trace (PicoSAT *, FILE * trace_file);
		_, err := C.picosat_write_extended_trace(p.p, cfile)
		return err
	})
}

// cFileWriterWrapper copies writeFn's data into w. writeFn takes a *C.FILE, and
// whatever writeFn writes to that *C.FILE, cFileWriterWrapper will then
// copy to w. This wrapper allows the Go API to write to io.Writers anything
// PicoSAT writes to a *C.FILE. writeFn need not close the *C.FILE.
func cFileWriterWrapper(w io.Writer, writeFn func(*C.FILE) error) (err error) {
	rp, wp, err := os.Pipe()
	if err != nil {
		return err
	}
	cfile, err := cfdopen(wp, "a") // wp.Close() below closes cfile.
	if err != nil {
		wp.Close()
		rp.Close()
		return err
	}

	// We have to read from the pipe in a separate goroutine because the write
	// end of the pipe will block if the pipe gets full.
	errChan := make(chan error, 1)
	go func() {
		_, e := io.Copy(w, rp)
		errChan <- e
	}()

	err = writeFn(cfile)
	// Without flushing cfile, the data might get stuck in the C buffer.
	if _, e := C.fflush(cfile); err == nil {
		err = e
	}
	// We have to close wp before rp or rp won't know the file has ended.
	if e := wp.Close(); err == nil {
		err = e
	}
	// We have to empty errChan to avoid data race between rp.Close and io.Copy.
	if e := <-errChan; err == nil {
		err = e
	}
	if e := rp.Close(); err == nil {
		err = e
	}
	return
}

// repeatWriteFn returns a writeFn for use with cFileWriterWrapper. The returned
// writeFn writes the byte in content to the file `times` number of times.
// If injected is a non-nil error, writeFn returns it instead of writing bytes.
// This function is only for testing cFileWriterWrapper and is in this file only
// because Cgo is not supported in test files. See TestCFileWriterWrapper
// in pigosat_test.go.
func repeatWriteFn(times int, content byte, injected error) func(*C.FILE) error {
	return func(file *C.FILE) error {
		if injected != nil {
			return injected
		}
		for i := 0; i < times; i++ {
			if _, e := C.fputc(C.int(content), file); e != nil {
				return e
			}
		}
		return nil
	}
}
