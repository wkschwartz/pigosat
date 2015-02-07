// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import (
	"fmt"
	"io/ioutil"
	"os"
	"testing"
	"time"
)

// abs takes the absolute value of an int32 and casts it to int.
func abs(x int32) int {
	if x < 0 {
		return int(-x)
	}
	return int(x)
}

// equal returns true if the two slices have the same contents.
func equal(x, y []bool) bool {
	if len(x) != len(y) {
		return false
	}
	for i := 0; i < len(x); i++ {
		if x[i] != y[i] {
			return false
		}
	}
	return true
}

// Evaluate a formula when the variables take on the values given by the
// solution.
func evaluate(formula [][]int32, solution []bool) bool {
	var c bool // The value for the clause
	for _, clause := range formula {
		c = false
		if len(clause) == 0 {
			continue
		}
		for _, literal := range clause {
			if literal > 0 && solution[abs(literal)] ||
				literal < 0 && !solution[abs(literal)] {
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

type formulaTest struct {
	formula   [][]int32
	variables int // count
	clauses   int // count
	status    int
	expected  []bool // solution
	onlyOne   bool   // No solution other than `expected` could satisfy
}

var formulaTests = []formulaTest{
	// The first three tests are cribbed from Ilan Schnell's Pycosat. See
	// https://github.com/ContinuumIO/pycosat. In particular, these are from
	// commit d81df1e in test_pycosat.py.
	0: {[][]int32{{1, -5, 4}, {-1, 5, 3, 4}, {-3, -4}},
		5, 3, Satisfiable,
		[]bool{false, true, false, false, false, true}, false},
	1: {[][]int32{{-1}, {1}},
		1, 2, Unsatisfiable,
		nil, false},
	2: {[][]int32{{-1, 2}, {-1, -2}, {1, -2}},
		2, 3, Satisfiable,
		[]bool{false, false, false}, true},
	// For testing that empty clauses are skipped and 0s end clauses
	3: {[][]int32{{1, -5, 4, 0, 9}, {-1, 5, 3, 4, 0, 100}, {}, {-3, -4, 0}, nil},
		5, 3, Satisfiable,
		[]bool{false, true, false, false, false, true}, false},
	// Armin Biere, "Using High Performance SAT and QBF Solvers", presentation
	// given 2011-01-24, pp. 23-48,
	// http://fmv.jku.at/biere/talks/Biere-TPTPA11.pdf
	// From "DIMACS example 1"
	4: {[][]int32{{-2}, {-1, -3}, {1, 2}, {2, 3}},
		3, 4, Unsatisfiable, nil, false},
	// From "Satisfying Assignments Example 2"
	5: {[][]int32{{1, 2}, {-1, 2}, {-2, 1}},
		2, 3, Satisfiable,
		[]bool{false, true, true}, true},
	6: {[][]int32{{1, 2}, {-1, 2}, {-2, 1}, {-1}},
		2, 4, Unsatisfiable, nil, false},
	7: {[][]int32{{1, 2}, {-1, 2}, {-2, 1}, {-2}},
		2, 4, Unsatisfiable, nil, false},
	// From "ex3.cnf"
	8: {[][]int32{{1, 2, 3}, {1, 2, -3}, {1, -2, 3}, {1, -2, -3}, {4, 5, 6},
		{4, 5, -6}, {4, -5, 6}, {4, -5, -6}, {-1, -4}, {1, 4}},
		6, 10, Unsatisfiable, nil, false},
	// From "ex4.cnf"
	9: {[][]int32{{1, 2, 3}, {1, 2 - 3}, {1, -2, 3}, {1, -2, -3}, {4, 5, 6},
		{4, 5, -6}, {4, -5, 6}, {4, -5, -6}, {-1, -4}, {-1, 4}, {-1, -4}},
		6, 11, Satisfiable,
		[]bool{false, false, false, true, true, false, false}, false},
}

// Ensure our expected solutions are correct.
func init() {
	for i, ft := range formulaTests {
		if ft.status == Satisfiable && !evaluate(ft.formula, ft.expected) {
			panic(i)
		}
	}
}

func wasExpected(t *testing.T, i int, p *Pigosat, ft *formulaTest, status int,
	solution []bool) {
	if status != ft.status {
		t.Errorf("Test %d: Expected status %d but got %d", i, ft.status, status)
	}
	if !equal(solution, ft.expected) {
		t.Errorf("Test %d: Expected solution %v but got %v", i, ft.expected,
			solution)
	}
	if p.Variables() != ft.variables {
		t.Errorf("Test %d: Expected %d variables, got %d", i, ft.variables,
			p.Variables())
	}
	// If satisfiable, add 1 because solving adds a clause
	offset := 0
	if ft.status == Satisfiable {
		offset = 1
	}
	if p.AddedOriginalClauses() != ft.clauses+offset {
		t.Errorf("Test %d: Exepcted %d clauses, got %d", i, ft.clauses+offset,
			p.AddedOriginalClauses())
	}
	if s := p.Seconds(); s <= 0 || s > time.Millisecond {
		t.Errorf("Test %d: Test took a suspicious amount of time: %v", i, s)
	}
}

func TestFormulas(t *testing.T) {
	for i, ft := range formulaTests {
		p, _ := NewPigosat(nil)
		p.AddClauses(ft.formula)
		status, solution := p.Solve()
		wasExpected(t, i, p, &ft, status, solution)
	}
}

func TestIterSolve(t *testing.T) {
	var status int
	var this, last []bool // solutions
	for i, ft := range formulaTests {
		p, _ := NewPigosat(nil)
		p.AddClauses(ft.formula)
		count := 0
		for status, this = p.Solve(); status == Satisfiable; status, this = p.Solve() {
			if !evaluate(ft.formula, this) {
				t.Errorf("Test %d: Solution %v does not satisfy formula %v",
					i, this, ft.formula)
			}
			if equal(this, last) {
				t.Errorf("Test %d: Duplicate solution: %v", i, this)
			}
			last = this
			count++
		}
		if count < 2 && ft.status == Satisfiable && !ft.onlyOne {
			t.Errorf("Test %d: Only one solution", i)
		}
	}
}

func TestBlockSolution(t *testing.T) {
	for i, ft := range formulaTests {
		p, _ := NewPigosat(nil)

		// Test bad inputs: one too short (remember sol[0] is always blank)
		solution := make([]bool, p.Variables())
		if err := p.BlockSolution(solution); err == nil {
			t.Errorf("Test %d: Expected error when solution too short")
		}
		// Now it'll be one too long
		solution = append(solution, true)
		solution = append(solution, true)
		if err := p.BlockSolution(solution); err == nil {
			t.Errorf("Test %d: Expected error when solution too long")
		}

		// Solve should not return ft.expected if it's blocked
		if ft.status == Satisfiable && !ft.onlyOne {
			p.AddClauses(ft.formula)
			if err := p.BlockSolution(ft.expected); err != nil {
				t.Errorf("Test %d: Unexpected error from BlockSolution: %v", i, err)
			}
			_, solution = p.Solve()
			if !evaluate(ft.formula, solution) {
				t.Errorf("Test %d: Solution %v does not satisfy formula %v",
					i, solution, ft.formula)
			}
			if equal(solution, ft.expected) {
				t.Errorf("Test %d: Duplicate solution: %v", i, solution)
			}
		}
	}
}

// Also cribbed from Pycosat
func TestPropLimit(t *testing.T) {
	for i, ft := range formulaTests {
		if ft.status != Satisfiable || ft.onlyOne {
			continue
		}
		seenUn, seenSat := false, false
		for limit := uint64(1); limit < 20; limit++ {
			p, _ := NewPigosat(&Options{PropagationLimit: limit})
			p.AddClauses(ft.formula)
			status, solution := p.Solve()
			if status == Unknown {
				seenUn = true
				if seenSat {
					t.Errorf("Test %d: Status unexpectedly changed back to "+
						"Unknown at limit=%d", i, limit)
				}
			} else if status == Satisfiable {
				seenSat = true
				if !seenUn {
					t.Errorf("Test %d: Propagation limit %d had no effect",
						i, limit)
				}
				wasExpected(t, i, p, &ft, status, solution)
			} else {
				t.Error("unreachable")
			}
		}
		if !seenUn || !seenSat {
			t.Errorf("Test %d: seenUn=%v, seenSat=%v", i, seenUn, seenSat)
		}
	}
}

// Test Option.OutputFile, Option.Verbosity, and Option.Prefix all at once.
func TestOutput(t *testing.T) {
	for i, ft := range formulaTests {
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
		p, err := NewPigosat(&Options{Verbosity: 1, OutputFile: tmp, Prefix: prefix})
		if err != nil {
			t.Fatal(err)
		}
		p.AddClauses(ft.formula)
		_, _ = p.Solve()
		// Now we make sure the file was written.
		buf := make([]byte, len(prefix))
		if n, err := tmp.ReadAt(buf, 0); err != nil {
			// Something wrong with either Verbosity or OutputFile
			t.Errorf("Output file not written to: bytes read=%d, err=%v", n, err)
		}
		if s := string(buf); s != prefix {
			t.Errorf(`Wrong perfix: expected "%s" but got "%s"`, prefix, s)
		}
	}
}

// Without MeasureAllCalls, AddClasuses is not meausured. With it, it is.
func TestMeasureAllCalls(t *testing.T) {
	for i, ft := range formulaTests {
		p, _ := NewPigosat(nil)
		p.AddClauses(ft.formula)
		if p.Seconds() != 0 {
			t.Errorf("Test %d: Seconds without MeasureAllCalls should not "+
				"measure AddClauses, but p.Seconds() == %v", i, p.Seconds())
		}
		p, _ = NewPigosat(&Options{MeasureAllCalls: true})
		p.AddClauses(ft.formula)
		if p.Seconds() == 0 {
			t.Errorf("Test %d: Seconds with MeasureAllCalls should measure "+
				"AddClauses, but p.Seconds() == %v", i, p.Seconds())
		}
	}
}

// Test that nil method calls are no ops
func TestNil(t *testing.T) {
	var a, b *Pigosat
	b, _ = NewPigosat(nil)
	b.Delete()
	for name, p := range map[string]*Pigosat{"uninit": a, "deleted": b} {
		// No panicking
		p.Delete()
		p.AddClauses([][]int32{{1}, {2}})
		if p.Variables() != 0 {
			t.Errorf("Test %s: Expected 0 vars, got %d", name, p.Variables())
		}
		if c := p.AddedOriginalClauses(); c != 0 {
			t.Errorf("Test %s: Expected 0 clauses, got %d", name, c)
		}
		if p.Seconds() != 0 {
			t.Errorf("Test %s: Expected 0 seconds, got %v", name, p.Seconds())
		}
		if status, solution := p.Solve(); status != NotReady || solution != nil {
			t.Errorf("Test %s: Expected status %d and nil solution, got %d and %v",
				name, NotReady, status, solution)
		}
		if err := p.BlockSolution([]bool{}); err != nil {
			t.Errorf("Test %s: Expected no-op BlockSolution, got error: %v",
				name, err)
		}
	}
}

// Test our assumption about what Picosat we're using.
func TestPicosatVersion(t *testing.T) {
	if v := PicosatVersion(); v != "957" {
		t.Errorf("Expected Picosat version 957, got version %s", v)
	}
}

// This is the example from the README.
func Example_readme() {
	p, _ := NewPigosat(nil)
	p.AddClauses([][]int32{{1, 2}, {1}, {-2}})
	fmt.Printf("# variables == %d\n", p.Variables())
	fmt.Printf("# clauses == %d\n", p.AddedOriginalClauses())
	status, solution := p.Solve()
	if status == Satisfiable {
		fmt.Println("status == pigosat.Satisfiable")
	}
	fmt.Printf("len(solution) == %d\n", len(solution))
	fmt.Printf("solution[1] == %v\n", solution[1])
	fmt.Printf("solution[2] == %v\n", solution[2])
	// Output:
	// # variables == 2
	// # clauses == 3
	// status == pigosat.Satisfiable
	// len(solution) == 3
	// solution[1] == true
	// solution[2] == false
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
		p, _ := NewPigosat(nil)
		p.AddClauses(formula)
		_, _ = p.Solve()
	}
}

// BenchmarkCreate measures how long it takes just to create a new Pigosat
// object without any options.
func BenchmarkCreate(b *testing.B) {
	var p *Pigosat
	for i := 0; i < b.N; i++ {
		p, _ = NewPigosat(nil)
	}
	// Shut the compiler up about not using p.
	b.StopTimer()
	p.AddClauses(formulaTests[benchTest].formula)
}

// BenchmarkAddClauses measures how long it takes to add a formula to a Pigosat
// object that already exists.
func BenchmarkAddClauses(b *testing.B) {
	b.StopTimer()
	formula := formulaTests[benchTest].formula
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		p, _ := NewPigosat(nil)
		b.StartTimer()
		p.AddClauses(formula)
		b.StopTimer()
	}
}
