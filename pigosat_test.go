// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import (
	"fmt"
	"io/ioutil"
	"os"
	"reflect"
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

// equal returns true if the two slices have the same contents.
func equal(x, y Solution) bool {
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
func evaluate(formula Formula, solution Solution) bool {
	var c bool // The value for the clause
	var index int
	for _, clause := range formula {
		c = false
		if len(clause) == 0 {
			continue
		}
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
	// For testing that empty clauses are skipped and 0s end clauses
	3: {Formula{{1, -5, 4, 0, 9}, {-1, 5, 3, 4, 0, 100}, {}, {-3, -4, 0}, nil},
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
}

// Ensure our expected solutions are correct.
func init() {
	for i, ft := range formulaTests {
		if ft.status == Satisfiable && !evaluate(ft.formula, ft.expected) {
			panic(i)
		}
	}
}

func wasExpected(t *testing.T, i int, p *Pigosat, ft *formulaTest,
	status Status, solution Solution) {
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
		t.Errorf("Test %d: Expected %d clauses, got %d", i, ft.clauses+offset,
			p.AddedOriginalClauses())
	}
	if s := p.Seconds(); s <= 0 || s > time.Millisecond {
		t.Errorf("Test %d: Test took a suspicious amount of time: %v", i, s)
	}
}

func TestFormulas(t *testing.T) {
	for i, ft := range formulaTests {
		p, _ := New(nil)
		p.AddClauses(ft.formula)
		status, solution := p.Solve()
		wasExpected(t, i, p, &ft, status, solution)
	}
}

// TestIterSolveRes tests that Pigosat.Solve works as an iterator and that
// Pigosat.Res returns Solve's last status.
func TestIterSolveRes(t *testing.T) {
	var status, res Status
	var this, last Solution
	for i, ft := range formulaTests {
		p, _ := New(nil)
		p.AddClauses(ft.formula)
		count := 0
		if res = p.Res(); res != Unknown {
			t.Errorf("Test %d: Res = %d before Solve called", i, res)
		}
		for status, this = p.Solve(); status == Satisfiable; status, this = p.Solve() {
			if !evaluate(ft.formula, this) {
				t.Errorf("Test %d: Solution %v does not satisfy formula %v",
					i, this, ft.formula)
			}
			if equal(this, last) {
				t.Errorf("Test %d: Duplicate solution: %v", i, this)
			}
			if res = p.Res(); res != status {
				t.Errorf("Test %d: Status = %d != %d = Res", i, status, res)
			}
			last = this
			count++
		}
		if count < 2 && ft.status == Satisfiable && !ft.onlyOne {
			t.Errorf("Test %d: Only one solution", i)
		}
		if res = p.Res(); res != Unsatisfiable {
			t.Errorf("Test %d: Res = %d after Solve finished", i, res)
		}
	}
}

func TestBlockSolution(t *testing.T) {
	var status Status
	for i, ft := range formulaTests {
		p, _ := New(nil)

		// Test bad inputs: one too short (remember sol[0] is always blank)
		solution := make(Solution, p.Variables())
		if err := p.BlockSolution(solution); err == nil {
			t.Errorf("Test %d: Expected error when solution too short", i)
		}
		// Now it'll be one too long
		solution = append(solution, true)
		solution = append(solution, true)
		if err := p.BlockSolution(solution); err == nil {
			t.Errorf("Test %d: Expected error when solution too long", i)
		}

		// Solve should not return ft.expected if it's blocked
		if ft.status == Satisfiable && !ft.onlyOne {
			p.AddClauses(ft.formula)
			if err := p.BlockSolution(ft.expected); err != nil {
				t.Errorf("Test %d: Unexpected error from BlockSolution: %v", i, err)
			}
			status, solution = p.Solve()
			if status != ft.status {
				t.Errorf("Test %d: Got status %v, expected %v", i, status,
					ft.status)
			}
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
			p, _ := New(&Options{PropagationLimit: limit})
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
		p, err := New(&Options{Verbosity: 1, OutputFile: tmp, Prefix: prefix})
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
			t.Errorf(`Wrong prefix: expected "%s" but got "%s"`, prefix, s)
		}
	}
}

// Without MeasureAllCalls, AddClasuses is not measured. With it, it is.
func TestMeasureAllCalls(t *testing.T) {
	for i, ft := range formulaTests {
		p, _ := New(nil)
		p.AddClauses(ft.formula)
		if p.Seconds() != 0 {
			t.Errorf("Test %d: Seconds without MeasureAllCalls should not "+
				"measure AddClauses, but p.Seconds() == %v", i, p.Seconds())
		}
		p, _ = New(&Options{MeasureAllCalls: true})
		p.AddClauses(ft.formula)
		if p.Seconds() == 0 {
			t.Errorf("Test %d: Seconds with MeasureAllCalls should measure "+
				"AddClauses, but p.Seconds() == %v", i, p.Seconds())
		}
	}
}

func TestAssumptionsSucceeding(t *testing.T) {
	formula := formulaTests[0].formula

	successTests := []struct {
		// The literals which should be assumed true/false
		assumpts []Literal
		// The number of solutions that we expect to produce
		solutions int
	}{
		{[]Literal{1}, 10},
		{[]Literal{2}, 9},
		{[]Literal{3}, 6},
		{[]Literal{4, 5}, 4},
	}

	var status Status
	var sol Solution

	for _, at := range successTests {
		p, _ := New(nil)
		p.AddClauses(formula)

		count := -1
		for status = Satisfiable; status == Satisfiable; count++ {
			for _, lit := range at.assumpts {
				p.Assume(lit)
			}
			status, sol = p.Solve()
			p.BlockSolution(sol)
		}

		if count != at.solutions {
			t.Errorf("Expected %d solution(s) for assumptions %v; got %d",
				at.solutions, at.assumpts, count)
		}
	}
}

func TestAssumptionsFailing(t *testing.T) {
	p, _ := New(nil)
	p.AddClauses(formulaTests[0].formula)
	p.Assume(3)
	p.Assume(4)
	p.Assume(5)
	p.Solve()
	failed := []Literal{3, 4}

	if actual := p.FailedAssumptions(); !reflect.DeepEqual(failed, actual) {
		t.Errorf("Expected failed assumptions did not match; %v != %v", failed, actual)
	}

	for _, f := range failed {
		if !p.FailedAssumption(f) {
			t.Errorf("Expected literal %v to be a failed assumption", f)
		}
	}

	wanted1, wanted2 := []Literal{3, 5}, []Literal{5, 4}
	if a := p.MaxSatisfiableAssumptions(); !reflect.DeepEqual(a, wanted1) {
		t.Errorf("MaxSatisfiableAssumptions: Got %v wanted %v", a, wanted1)
	}
	if a := p.NextMaxSatisfiableAssumptions(); !reflect.DeepEqual(a, wanted1) {
		t.Errorf("NextMaxSatisfiableAssumptions: Got %v wanted %v", a, wanted1)
		}
	if a := p.NextMaxSatisfiableAssumptions(); !reflect.DeepEqual(a, wanted2) {
		t.Errorf("NextMaxSatisfiableAssumptions: Got %v wanted %v", a, wanted2)
	}
	if a := p.NextMaxSatisfiableAssumptions(); !reflect.DeepEqual(a, []Literal{}) {
		t.Errorf("NextMaxSatisfiableAssumptions: Got %v wanted %v", a, []Literal{})
	}
}

// Assert that function f panics when called. test is a string identifying which
// input data are being tested. method is a string identifying which method is
// being tested in f.
func assertPanics(t *testing.T, test, method string, f func()) {
	defer func() {
		if r := recover(); r == nil {
			t.Errorf("Test %s: %s failed to panic", test, method)
		}
	}()
	f()
}

// Test that method calls on uninitialized or deleted objects panic
func TestUninitializedOrDeleted(t *testing.T) {
	var a, b *Pigosat
	b, _ = New(nil)
	b.delete()
	for name, p := range map[string]*Pigosat{"uninit": a, "deleted": b} {
		assertPanics(t, name, "AddClauses", func() {
			p.AddClauses(Formula{{1}, {2}})
		})
		assertPanics(t, name, "Variables", func() { p.Variables() })
		assertPanics(t, name, "AddedOriginalClauses", func() {
			p.AddedOriginalClauses()
		})
		assertPanics(t, name, "Seconds", func() { p.Seconds() })
		assertPanics(t, name, "Solve", func() { p.Solve() })
		assertPanics(t, name, "BlockSolution", func() {
			p.BlockSolution(Solution{})
		})
		assertPanics(t, name, "Print", func() { p.Print(nil) })
	}
}

func TestPrint(t *testing.T) {
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
		p, err := New(nil)
		p.AddClauses(ft.formula)
		p.Print(tmp)
		// Now we make sure the file was written.
		buf, err := ioutil.ReadFile(tmp.Name())
		if err != nil {
			t.Errorf("Test %d: Output file not written to: err=%v", i, err)
		}
		if s := string(buf); s != ft.dimacs {
			t.Errorf("Test %d: expected >>>\n%s<<< but got >>>\n%s<<<", i,
				ft.dimacs, s)
		}
	}
}

func TestlitArrayToSlice(t *testing.T) {
	// null pointers
	assertPanics(t, "null pointer", "litArrayToSlice",
		func() { litArrayToSlice(nil, 0) })
	assertPanics(t, "null pointer", "litArrayToSlice",
		func() { litArrayToSlice(nil, 1) })
	// not zero terminated
	badPtr := &cArray123[0]
	assertPanics(t, "not zero terminated - unpadded", "litArrayToSlice",
		func() { litArrayToSlice(badPtr, 3) })
	assertPanics(t, "not zero terminated - padded", "litArrayToSlice",
		func() { litArrayToSlice(badPtr, 2) })
	// zero length
	if ls := litArrayToSlice(&cZero, 0); len(ls) != 0 {
		t.Errorf("Test 0-length litArrayToSlice, maxLen==0: return value has length %d",
			len(ls))
	}
	if ls := litArrayToSlice(&cZero, 1); len(ls) != 0 {
		t.Errorf(
			"Test 0-length litArrayToSlice, maxLen>0: return value has length %d",
			len(ls))
	}
	// works correctly
	ptr := &cArray1230[0]
	expected := []Literal{1, 2, 3}
	if ls := litArrayToSlice(ptr, 3); len(ls) != 3 || !reflect.DeepEqual(ls, expected) {
		t.Errorf(
			"Test litArrayToSlice correct, maxLen==3: expected %v but got %v",
			expected, ls)
	}
	if ls := litArrayToSlice(ptr, 4); len(ls) != 3 || !reflect.DeepEqual(ls, expected) {
		t.Errorf(
			"Test litArrayToSlice correct, maxLen==4: expected %v but got %v",
			expected, ls)
	}
}

// This is the example from the README.
func Example_readme() {
	p, _ := New(nil)
	p.AddClauses(Formula{{1, 2}, {1}, {-2}})
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
		p, _ := New(nil)
		p.AddClauses(formula)
		_, _ = p.Solve()
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
	p.AddClauses(formulaTests[benchTest].formula)
}

// BenchmarkAddClauses measures how long it takes to add a formula to a Pigosat
// object that already exists.
func BenchmarkAddClauses(b *testing.B) {
	b.StopTimer()
	formula := formulaTests[benchTest].formula
	b.ResetTimer()
	for i := 0; i < b.N; i++ {
		p, _ := New(nil)
		b.StartTimer()
		p.AddClauses(formula)
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
		p.AddClauses(formulaTests[benchTest].formula)
		b.StartTimer()
		p.BlockSolution(solution)
		b.StopTimer()
	}
}
