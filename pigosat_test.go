// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import "testing"
import "time"
import "fmt"

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
}

var formulaTests = []formulaTest{
	// The first three tests are cribbed from Ilan Schnell's Pycosat. See
	// https://github.com/ContinuumIO/pycosat. In particular, these are from
	// commit d81df1e in test_pycosat.py.
	0: {[][]int32{{1, -5, 4}, {-1, 5, 3, 4}, {-3, -4}},
		5, 3, Satisfiable,
		[]bool{false, true, false, false, false, true}},
	1: {[][]int32{{-1}, {1}},
		1, 2, Unsatisfiable,
		nil},
	2: {[][]int32{{-1, 2}, {-1, -2}, {1, -2}},
		2, 3, Satisfiable,
		[]bool{false, false, false}},
	// For testing that empty clauses are skipped and 0s end clauses
	3: {[][]int32{{1, -5, 4, 0, 9}, {-1, 5, 3, 4, 0, 100}, {}, {-3, -4, 0}, nil},
		5, 3, Satisfiable,
		[]bool{false, true, false, false, false, true}},
	// Armin Biere, "Using High Performance SAT and QBF Solvers", presentation
	// given 2011-01-24, pp. 23-48,
	// http://fmv.jku.at/biere/talks/Biere-TPTPA11.pdf
	// From "DIMACS example 1"
	4: {[][]int32{{-2}, {-1, -3}, {1, 2}, {2, 3}},
		3, 4, Unsatisfiable, nil},
	// From "Satisfying Assignments Example 2"
	5: {[][]int32{{1, 2}, {-1, 2}, {-2, 1}},
		2, 3, Satisfiable,
		[]bool{false, true, true}},
	6: {[][]int32{{1, 2}, {-1, 2}, {-2, 1}, {-1}},
		2, 4, Unsatisfiable, nil},
	7: {[][]int32{{1, 2}, {-1, 2}, {-2, 1}, {-2}},
		2, 4, Unsatisfiable, nil},
	// From "ex3.cnf"
	8: {[][]int32{{1, 2, 3}, {1, 2, -3}, {1, -2, 3}, {1, -2, -3}, {4, 5, 6},
		{4, 5, -6}, {4, -5, 6}, {4, -5, -6}, {-1, -4}, {1, 4}},
		6, 10, Unsatisfiable, nil},
	// From "ex4.cnf"
	9: {[][]int32{{1, 2, 3}, {1, 2 - 3}, {1, -2, 3}, {1, -2, -3}, {4, 5, 6},
		{4, 5, -6}, {4, -5, 6}, {4, -5, -6}, {-1, -4}, {-1, 4}, {-1, -4}},
		6, 11, Satisfiable, []bool{false, false, false, true, true, false, false}},
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
	if p.AddedOriginalClauses() != ft.clauses {
		t.Errorf("Test %d: Exepcted %d clauses, got %d", i, ft.clauses,
			p.AddedOriginalClauses())
	}
	if s := p.Seconds(); s <= 0 || s > time.Millisecond {
		t.Errorf("Test %d: Test took a suspicious amount of time: %v", i, s)
	}
}

func TestFormulas(t *testing.T) {
	var p *Pigosat
	var status int
	var solution []bool
	for i, ft := range formulaTests {
		p = NewPigosat(0)
		p.AddClauses(ft.formula)
		status, solution = p.Solve()
		wasExpected(t, i, p, &ft, status, solution)
		p.Delete()
	}
}

// Also cribbed from Pycosat
func TestPropLimit(t *testing.T) {
	var p *Pigosat
	var status int
	var solution []bool
	ft := formulaTests[0]
	var limit uint64
	for limit = 1; limit < 20; limit++ {
		p = NewPigosat(limit)
		p.AddClauses(ft.formula)
		status, solution = p.Solve()
		if limit < 8 {
			if status != Unknown {
				t.Errorf("Propagation limit %d had no effect on formula 0",
					limit)
			}
			p.Delete()
			continue
		}
		wasExpected(t, 0, p, &ft, status, solution)
		p.Delete()
	}
}

// Test that nil method calls are no ops
func TestNil(t *testing.T) {
	var a, b *Pigosat
	b = NewPigosat(0)
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
	p := NewPigosat(0)
	defer p.Delete()
	p.AddClauses([][]int32{{1, 2}, {-2}})
	fmt.Println("")
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
	// # clauses == 2
	// status == pigosat.Satisfiable
	// len(solution) == 3
	// solution[1] == true
	// solution[2] == false
}
