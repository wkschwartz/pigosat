// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import (
	"bytes"
	"fmt"
	"io/ioutil"
	"os"
	"reflect"
	"runtime"
	"sort"
	"strings"
	"testing"
	"time"
)

// abs takes the absolute value of an Literal and casts it to int.
func abs(x Literal) int {
	if x < 0 {
		return int(-x)
	}
	return int(x)
}

// Evaluate a formula when the variables take on the values given by the
// solution.
func evaluate(formula Formula, solution Solution) bool {
	var c bool // The value for the clause
	var index int
	for _, clause := range formula {
		c = false
		for _, literal := range clause {
			index = abs(literal)
			// Solution isn't even the right length
			if index >= len(solution) {
				return false
			}
			if literal > 0 && solution[index] ||
				literal < 0 && !solution[index] {
				c = true
				break
			}
		}
		if !c {
			return false
		}
	}
	return true
}

func equalDimacs(d1, d2 string) bool {
	// We can't rely on the DIMACS output having clauses in a consistent order,
	// so we compare the output as a sorted list of lines.
	actual := strings.Split(d1, "\n")
	expected := strings.Split(d2, "\n")
	sort.Strings(actual)
	sort.Strings(expected)
	return reflect.DeepEqual(actual, expected)
}

type formulaTest struct {
	formula   Formula
	variables int // count
	clauses   int // count
	status    Status
	expected  Solution
	onlyOne   bool   // No solution other than `expected` could satisfy
	dimacs    string // DIMACS-format CNF
}

var formulaTests = []formulaTest{
	// The first three tests are cribbed from Ilan Schnell's Pycosat. See
	// https://github.com/ContinuumIO/pycosat. In particular, these are from
	// commit d81df1e in test_pycosat.py.
	0: {Formula{{1, -5, 4}, {-1, 5, 3, 4}, {-3, -4}},
		5, 3, Satisfiable,
		Solution{false, true, false, false, false, true}, false,
		`p cnf 5 3
1 4 -5 0
-1 3 4 5 0
-3 -4 0
`},
	1: {Formula{{-1}, {1}},
		1, 2, Unsatisfiable,
		nil, false,
		`p cnf 1 3
-1 0
1 0
0
`},
	2: {Formula{{-1, 2}, {-1, -2}, {1, -2}},
		2, 3, Satisfiable,
		Solution{false, false, false}, true,
		`p cnf 2 3
1 -2 0
-1 2 0
-1 -2 0
`},
	// For testing that 0s end clauses
	3: {Formula{{1, -5, 4, 0, 9}, {-1, 5, 3, 4, 0, 100}, {-3, -4, 0}},
		5, 3, Satisfiable,
		Solution{false, true, false, false, false, true}, false,
		`p cnf 5 3
1 4 -5 0
-1 3 4 5 0
-3 -4 0
`},
	// Armin Biere, "Using High Performance SAT and QBF Solvers", presentation
	// given 2011-01-24, pp. 23-48,
	// http://fmv.jku.at/biere/talks/Biere-TPTPA11.pdf
	// From "DIMACS example 1"
	4: {Formula{{-2}, {-1, -3}, {1, 2}, {2, 3}},
		3, 4, Unsatisfiable, nil, false,
		`p cnf 3 6
-2 0
1 0
3 0
1 2 0
-1 -3 0
2 3 0
`},
	// From "Satisfying Assignments Example 2"
	5: {Formula{{1, 2}, {-1, 2}, {-2, 1}},
		2, 3, Satisfiable,
		Solution{false, true, true}, true,
		`p cnf 2 3
1 2 0
1 -2 0
-1 2 0
`},
	6: {Formula{{1, 2}, {-1, 2}, {-2, 1}, {-1}},
		2, 4, Unsatisfiable, nil, false,
		`p cnf 2 4
-1 0
1 2 0
1 -2 0
-1 2 0
`},
	7: {Formula{{1, 2}, {-1, 2}, {-2, 1}, {-2}},
		2, 4, Unsatisfiable, nil, false,
		`p cnf 2 4
-2 0
1 2 0
1 -2 0
-1 2 0
`},
	// From "ex3.cnf"
	8: {Formula{{1, 2, 3}, {1, 2, -3}, {1, -2, 3}, {1, -2, -3}, {4, 5, 6},
		{4, 5, -6}, {4, -5, 6}, {4, -5, -6}, {-1, -4}, {1, 4}},
		6, 10, Unsatisfiable, nil, false,
		`p cnf 6 10
1 2 3 0
1 2 -3 0
1 -2 3 0
1 -2 -3 0
4 5 6 0
4 5 -6 0
4 -5 6 0
4 -5 -6 0
1 4 0
-1 -4 0
`},
	// From "ex4.cnf"
	9: {Formula{{1, 2, 3}, {1, 2 - 3}, {1, -2, 3}, {1, -2, -3}, {4, 5, 6},
		{4, 5, -6}, {4, -5, 6}, {4, -5, -6}, {-1, -4}, {-1, 4}, {-1, -4}},
		6, 11, Satisfiable,
		Solution{false, false, false, true, true, false, false}, false,
		`p cnf 6 10
1 2 3 0
1 -2 3 0
1 -2 -3 0
4 5 6 0
4 5 -6 0
4 -5 6 0
4 -5 -6 0
-1 -4 0
-1 4 0
-1 -4 0
`},
	// Adding empty clauses causes Solve to deduce Unsatisfiable
	10: {Formula{{1, 2}, {}},
		2, 2, Unsatisfiable, nil, false,
		`p cnf 2 2
1 2 0
0
`},
	11: {Formula{{1, 2}, nil},
		2, 2, Unsatisfiable, nil, false,
		`p cnf 2 2
1 2 0
0
`},
}

// Ensure our expected solutions are correct.
func init() {
	for i, ft := range formulaTests {
		if ft.status == Satisfiable && !evaluate(ft.formula, ft.expected) {
			panic(i)
		}
	}
}

func wasExpected(t *testing.T, p *Pigosat, ft *formulaTest,
	status Status, solution Solution) {
	if status != ft.status {
		t.Errorf("Expected status %d but got %d", ft.status, status)
	}
	if !reflect.DeepEqual(solution, ft.expected) {
		t.Errorf("Expected solution %v but got %v", ft.expected,
			solution)
	}
	if p.Variables() != ft.variables {
		t.Errorf("Expected %d variables, got %d", ft.variables,
			p.Variables())
	}
	if p.AddedOriginalClauses() != ft.clauses {
		t.Errorf("Expected %d clauses, got %d", ft.clauses,
			p.AddedOriginalClauses())
	}
	if s := p.Seconds(); s < 0 || s > time.Millisecond {
		t.Errorf("Test took a suspicious amount of time: %v", s)
	}
}

func TestFormulas(t *testing.T) {
	for i, ft := range formulaTests {
		t.Run(fmt.Sprintf("formulaTests[%d]", i), func(t *testing.T) {
			p, _ := New(nil)
			p.Add(ft.formula)
			solution, status := p.Solve()
			wasExpected(t, p, &ft, status, solution)
		})
	}
}

// TestIterSolveRes tests that Pigosat.Solve works as an iterator and that
// Pigosat.Res returns Solve's last status.
func TestIterSolveRes(t *testing.T) {
	var status, res Status
	var this, last Solution
	for i, ft := range formulaTests {
		t.Run(fmt.Sprintf("formulaTests[%d]", i), func(t *testing.T) {
			p, _ := New(nil)
			p.Add(ft.formula)
			count := 0
			if res = p.Res(); res != Unknown {
				t.Errorf("Res = %d before Solve called", res)
			}
			for this, status = p.Solve(); status == Satisfiable; this, status = p.Solve() {
				if !evaluate(ft.formula, this) {
					t.Errorf("Solution %v does not satisfy formula %v",
						this, ft.formula)
				}
				if reflect.DeepEqual(this, last) {
					t.Errorf("Duplicate solution: %v", this)
				}
				if res = p.Res(); res != status {
					t.Errorf("Status = %d != %d = Res", status, res)
				}
				last = this
				count++
				p.BlockSolution(this)
			}
			if count < 2 && ft.status == Satisfiable && !ft.onlyOne {
				t.Errorf("Only one solution")
			}
			if res = p.Res(); res != Unsatisfiable {
				t.Errorf("Res = %d after Solve finished", res)
			}
		})
	}
}

func TestBlockSolution(t *testing.T) {
	var status Status
	for i, ft := range formulaTests {
		t.Run(fmt.Sprintf("formulaTests[%d]", i), func(t *testing.T) {
			p, _ := New(nil)

			// Test bad inputs: one too short (remember sol[0] is always blank)
			solution := make(Solution, p.Variables())
			if err := p.BlockSolution(solution); err == nil {
				t.Errorf("Expected error when solution too short")
			}
			// Now it'll be one too long
			solution = append(solution, true)
			solution = append(solution, true)
			if err := p.BlockSolution(solution); err == nil {
				t.Errorf("Expected error when solution too long")
			}

			// Solve should not return ft.expected if it's blocked
			if ft.status == Satisfiable && !ft.onlyOne {
				p.Add(ft.formula)
				if err := p.BlockSolution(ft.expected); err != nil {
					t.Errorf("Unexpected error from BlockSolution: %v", err)
				}
				solution, status = p.Solve()
				if status != ft.status {
					t.Errorf("Got status %v, expected %v", status,
						ft.status)
				}
				if !evaluate(ft.formula, solution) {
					t.Errorf("Solution %v does not satisfy formula %v",
						solution, ft.formula)
				}
				if reflect.DeepEqual(solution, ft.expected) {
					t.Errorf("Duplicate solution: %v", solution)
				}
			}
		})
	}
}

// Also cribbed from Pycosat
func TestPropLimit(t *testing.T) {
	for i, ft := range formulaTests {
		t.Run(fmt.Sprintf("formulaTests[%d]", i), func(t *testing.T) {
			if ft.status != Satisfiable || ft.onlyOne {
				return
			}
			seenUn, seenSat := false, false
			for limit := uint64(1); limit < 20; limit++ {
				p, _ := New(&Options{PropagationLimit: limit})
				p.Add(ft.formula)
				solution, status := p.Solve()
				if status == Unknown {
					seenUn = true
					if seenSat {
						t.Errorf("Status unexpectedly changed back to "+
							"Unknown at limit=%d", limit)
					}
				} else if status == Satisfiable {
					seenSat = true
					if !seenUn {
						t.Errorf("Propagation limit %d had no effect", limit)
					}
					wasExpected(t, p, &ft, status, solution)
				} else {
					t.Error("unreachable")
				}
			}
			if !seenUn || !seenSat {
				t.Errorf("seenUn=%v, seenSat=%v", seenUn, seenSat)
			}
		})
	}
}

// Test Option.OutputFile, Option.Verbosity, and Option.Prefix all at once.
func TestOutput(t *testing.T) {
	for i, ft := range formulaTests {
		t.Run(fmt.Sprintf("formulaTests[%d]", i), func(t *testing.T) {
			tmp, err := ioutil.TempFile("", "")
			if err != nil {
				t.Fatal(err)
			}
			defer func() {
				tmp.Close()
				if err := os.Remove(tmp.Name()); err != nil {
					t.Error(err)
				}
			}()
			prefix := fmt.Sprintf("asdf%x ", i)
			p, err := New(&Options{Verbosity: 1, OutputFile: tmp, Prefix: prefix})
			if err != nil {
				t.Fatal(err)
			}
			p.Add(ft.formula)
			p.Solve()
			// Ensure that closing p doesn't close the OutputFile.
			p.Delete()
			// Now we make sure the file was written.
			buf := make([]byte, len(prefix))
			if n, err := tmp.ReadAt(buf, 0); err != nil {
				// Something wrong with either Verbosity or OutputFile
				t.Errorf("Output file not written to: bytes read=%d, err=%v", n, err)
			}
			if s := string(buf); s != prefix {
				t.Errorf(`Wrong prefix: expected "%s" but got "%s"`, prefix, s)
			}
		})
	}
}

// Without MeasureAllCalls, AddClasuses is not measured. With it, it is.
func TestMeasureAllCalls(t *testing.T) {
	for i, ft := range formulaTests {
		t.Run(fmt.Sprintf("formulaTests[%d]", i), func(t *testing.T) {
			p, _ := New(nil)
			p.Add(ft.formula)
			if p.Seconds() != 0 {
				t.Errorf("Seconds without MeasureAllCalls should not "+
					"measure Add, but p.Seconds() == %v", p.Seconds())
			}
			p, _ = New(&Options{MeasureAllCalls: true})
			p.Add(ft.formula)
			if p.Seconds() == 0 {
				t.Errorf("Seconds with MeasureAllCalls should measure "+
					"Add, but p.Seconds() == %v", p.Seconds())
			}
		})
	}
}

// Assert that function f panics when called. test is a string identifying which
// input data are being tested. method is a string identifying which method is
// being tested in f.
func assertPanics(t *testing.T, method string, f func()) {
	defer func() {
		if r := recover(); r == nil {
			t.Errorf("%s failed to panic", method)
		}
	}()
	f()
}

// Test that method calls on uninitialized or deleted objects panic
func TestUninitializedOrDeleted(t *testing.T) {
	var a, b *Pigosat
	b, _ = New(nil)
	b.Delete()
	for name, p := range map[string]*Pigosat{"uninit": a, "deleted": b} {
		t.Run(name, func(t *testing.T) {
			assertPanics(t, "Add", func() { p.Add(Formula{{1}, {2}}) })
			assertPanics(t, "Variables", func() { p.Variables() })
			assertPanics(t, "AddedOriginalClauses", func() {
				p.AddedOriginalClauses()
			})
			assertPanics(t, "Seconds", func() { p.Seconds() })
			assertPanics(t, "Solve", func() { p.Solve() })
			assertPanics(t, "BlockSolution", func() {
				p.BlockSolution(Solution{})
			})
			assertPanics(t, "Print", func() { p.Print(nil) })
			assertPanics(t, "Res", func() { p.Res() })
			assertPanics(t, "WriteClausalCore", func() {
				var buf *bytes.Buffer
				p.WriteClausalCore(buf)
			})
			assertPanics(t, "WriteCompactTrace", func() {
				var buf *bytes.Buffer
				p.WriteCompactTrace(buf)
			})
			assertPanics(t, "WriteExtendedTrace", func() {
				var buf *bytes.Buffer
				p.WriteExtendedTrace(buf)
			})

			assertPanics(t, "Assume", func() { p.Assume(1) })
			assertPanics(t, "FailedAssumption", func() {
				p.FailedAssumption(1)
			})
			assertPanics(t, "FailedAssumptions", func() {
				p.FailedAssumptions()
			})
			assertPanics(t, "MaxSatisfiableAssumptions", func() {
				p.MaxSatisfiableAssumptions()
			})
			assertPanics(t, "NextMaxSatisfiableAssumptions", func() {
				p.NextMaxSatisfiableAssumptions()
			})
		})
	}
}

func TestCFileWriterWrapper(t *testing.T) {
	var buf bytes.Buffer
	// Pick something bigger than pipe buffers usually get. See
	//   1. http://unix.stackexchange.com/a/11954/17035
	//   2. http://man7.org/linux/man-pages/man7/pipe.7.html
	// On Mac OS and Linux, it seems pipes fill up at 65536 bytes. This is large
	// enough to  elicit a deadlock in incorrect implementations.
	const size int = 1<<16 + 1<<15
	const content byte = 'a'
	err := cFileWriterWrapper(&buf, repeatWriteFn(size, content, nil))
	if err != nil {
		t.Error(err)
	}
	if buf.Len() != size {
		t.Errorf("Only %d of %d bytes written to buffer", buf.Len(), size)
	}
	if s := buf.String(); s[0] != content || s[len(s)-1] != content {
		t.Errorf("Buffer does not contain the expected data")
	}

	// Test that the goroutine the copies from the pipe to the io.Writer does
	// not leak if cFileWriterWrapper exits early because of an error after
	// the goroutine starts. We do this by injecting an error from the writeFn.
	// Do not mark this test as being parallelizable (using t.Parallel())
	// because it counts the number of goroutines.
	fakeError := fmt.Errorf("fake error")
	num_goroutines_before := runtime.NumGoroutine()
	err = cFileWriterWrapper(&buf, repeatWriteFn(size, content, fakeError))
	time.Sleep(100 * time.Microsecond) // Give goroutine enough time to finish
	num_goroutines_after := runtime.NumGoroutine()
	if err != fakeError {
		t.Error(err)
	}
	if num_goroutines_after != num_goroutines_before {
		t.Errorf("Possible goroutine leak. Before calling cFileWriterWrapper "+
			"there were %d goroutines, and afterward there were %d.",
			num_goroutines_before, num_goroutines_after)
	}
}

func TestPrint(t *testing.T) {
	var buf bytes.Buffer
	for i, ft := range formulaTests {
		t.Run(fmt.Sprintf("formulaTests[%d]", i), func(t *testing.T) {
			buf.Reset()
			p, _ := New(nil)
			p.Add(ft.formula)
			err := p.Print(&buf)
			if err != nil {
				t.Errorf("Output file not written to: err=%v", err)
			}
			if !equalDimacs(buf.String(), ft.dimacs) {
				t.Errorf("expected >>>\n%s<<< but got >>>\n%s<<<",
					ft.dimacs, buf.String())
			}
		})
	}
}

func TestWriteClausalCore(t *testing.T) {
	var buf bytes.Buffer
	prefix := []byte(`p cnf`)

	for i, ft := range formulaTests {
		t.Run(fmt.Sprintf("formulaTests[%d]", i), func(t *testing.T) {
			p, _ := New(&Options{EnableTrace: true})
			p.Add(ft.formula)
			_, status := p.Solve()

			buf.Reset()
			err := p.WriteClausalCore(&buf)

			// Only Unsatisfiable solutions should produce clausal cores.
			if err != nil {
				if status == Unsatisfiable {
					t.Errorf("Error calling WriteClausalCore: %v", err)
				}
				return
			}

			// Just make sure we write out a valid DIMACS format since we are only
			// testing the API here, not the solutions.
			if !bytes.HasPrefix(buf.Bytes(), prefix) {
				t.Errorf("Expected Unsatisfiable clausal core to "+
					"start with 'p cnf'; got %q", buf)
			}
		})
	}
}

func TestWriteTrace(t *testing.T) {
	var buf bytes.Buffer

	for i, ft := range formulaTests {
		t.Run(fmt.Sprintf("formulaTests[%d]", i), func(t *testing.T) {
			p, _ := New(&Options{EnableTrace: true})
			p.Add(ft.formula)
			_, status := p.Solve()

			buf.Reset()
			err := p.WriteCompactTrace(&buf)

			// Only Unsatisfiable solutions should produce a trace
			if err != nil {
				if status == Unsatisfiable {
					t.Errorf("Error calling WriteCompactTrace: %v", err)
				}
				return
			}
			if buf.Len() == 0 {
				t.Errorf("Unsatisfiable formula to produced no compact trace")
			}

			buf.Reset()
			err = p.WriteExtendedTrace(&buf)

			// Only Unsatisfiable solutions should produce a trace
			if err != nil {
				if status == Unsatisfiable {
					t.Errorf("Error calling WriteExtendedTrace: %v", err)
				}
				return
			}
			if buf.Len() == 0 {
				t.Errorf("Unsatisfiable formula to produced no extended trace")
			}
		})
	}
}

func TestSolutionString(t *testing.T) {
	const expectedString = "{1:true , 2:false, 3:false, 4:false, 5:true}"
	if s := formulaTests[0].expected.String(); s != expectedString {
		t.Errorf("Expected %v. Got %v.", expectedString, s)
	}
	if s := (Solution{}).String(); s != "{}" {
		t.Errorf("Expected {}. Got %v", s)
	}
	if s := (Solution{false}).String(); s != "{}" {
		t.Errorf("Expected {}. Got %v", s)
	}
	if s := (Solution{false, true}).String(); s != "{1:true}" {
		t.Errorf("Expected {1:true}. Got %v", s)
	}
	if s := (Solution{false, true, true}).String(); s != "{1:true , 2:true}" {
		t.Errorf("Expected {1:true, 2:true}. Got %v", s)
	}
}

func TestStatusString(t *testing.T) {
	if s := Unknown.String(); s != "Unknown" {
		t.Errorf(`Expected "Unknown". Got %v`, s)
	}
	if s := Satisfiable.String(); s != "Satisfiable" {
		t.Errorf(`Expected "Satisfiable". Got %v`, s)
	}
	if s := Unsatisfiable.String(); s != "Unsatisfiable" {
		t.Errorf(`Expected "Unsatisfiable". Got %v`, s)
	}
	if s := Status(17).String(); s != "Status(17)" {
		t.Errorf(`Expected "Status(17)". Got %v`, s)
	}
}

func Example() {
	p, _ := New(nil)

	// Calling Delete is not usually necessary. Advanced users, see Delete's
	// documentation.
	defer p.Delete()

	p.Add(Formula{{1, 2, -3}, {3, 4}})
	fmt.Printf("Number of variables == %d\n", p.Variables())
	fmt.Printf("Number of clauses   == %d\n", p.AddedOriginalClauses())
	solution, status := p.Solve()
	fmt.Println(status, "solution ==", solution)
	fmt.Printf("                     == %#v\n", solution)
	p.BlockSolution(solution)
	fmt.Println("\nMore solutions:")
	for solution, status := p.Solve(); status == Satisfiable; solution, status = p.Solve() {
		fmt.Println(status, "solution ==", solution)
		p.BlockSolution(solution)
	}
	// Output:
	// Number of variables == 4
	// Number of clauses   == 2
	// Satisfiable solution == {1:true , 2:true , 3:true , 4:true}
	//                      == pigosat.Solution{false, true, true, true, true}
	//
	// More solutions:
	// Satisfiable solution == {1:true , 2:true , 3:true , 4:false}
	// Satisfiable solution == {1:true , 2:true , 3:false, 4:true}
	// Satisfiable solution == {1:true , 2:false, 3:false, 4:true}
	// Satisfiable solution == {1:true , 2:false, 3:true , 4:true}
	// Satisfiable solution == {1:true , 2:false, 3:true , 4:false}
	// Satisfiable solution == {1:false, 2:false, 3:false, 4:true}
	// Satisfiable solution == {1:false, 2:true , 3:false, 4:true}
	// Satisfiable solution == {1:false, 2:true , 3:true , 4:true}
	// Satisfiable solution == {1:false, 2:true , 3:true , 4:false}
}

// The element of formulaTests to use for benchmarking. This one is a longer
// test, so we might pick up more speed effects with it.
const benchTest = 9

// BenchmarkSolve measures how long it takes to create and solve a Pigosat
// instance.
func BenchmarkSolve(b *testing.B) {
	formula := formulaTests[benchTest].formula
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		p, _ := New(nil)
		p.Add(formula)
		p.Solve()
	}
}

// BenchmarkCreate measures how long it takes just to create a new Pigosat
// object without any options.
func BenchmarkCreate(b *testing.B) {
	var p *Pigosat
	for i := 0; i < b.N; i++ {
		p, _ = New(nil)
	}
	// Shut the compiler up about not using p.
	b.StopTimer()
	p.Add(formulaTests[benchTest].formula)
}

// BenchmarkAdd measures how long it takes to add a formula to a Pigosat object
// that already exists.
func BenchmarkAdd(b *testing.B) {
	b.StopTimer()
	formula := formulaTests[benchTest].formula
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		p, _ := New(nil)
		b.StartTimer()
		p.Add(formula)
		b.StopTimer()
	}
}

// BenchmarkBlockSolution measures how long it takes to add a clause negating
// the last solution.
func BenchmarkBlockSolution(b *testing.B) {
	b.StopTimer()
	solution := formulaTests[benchTest].expected
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		p, _ := New(nil)
		p.Add(formulaTests[benchTest].formula)
		b.StartTimer()
		p.BlockSolution(solution)
		b.StopTimer()
	}
}
