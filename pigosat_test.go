package pigosat

import "testing"

// abs takes the absolute value of an int32 and casts it to int.
func abs(x int32) int {
	if x < 0 {
		return int(-x)
	}
	return int(x)
}

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
	formula [][]int32
	variables int // count
	status int
	expected []bool // solution
}

// The first three tests are cribbed from Ilan Schnell's Pycosat. See
// https://github.com/ContinuumIO/pycosat. In particular, these are from commit
// d81df1e in test_pycosat.py.
var formulaTests = []formulaTest{
	{[][]int32{{1, -5, 4}, {-1, 5, 3, 4}, {-3, -4}},
		5, Satisfiable,
		[]bool{false, true, false, false, false, true}},
	{[][]int32{{-1}, {1}},
		1, Unsatisfiable,
		nil},
	{[][]int32{{-1, 2}, {-1, -2}, {1, -2}},
		2, Satisfiable,
		[]bool{false, false, false}},
}

// Ensure our expected solutions are correct.
func init() {
	for i, ft := range formulaTests {
		if ft.status == Satisfiable && !evaluate(ft.formula, ft.expected) {
			panic(i)
		}
	}
}


func wasExpected(t *testing.T, i int, p *Picosat, ft *formulaTest, status int,
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
	if p.AddedOriginalClauses() != len(ft.formula) {
		t.Errorf("Test %d: Exepcted %d clauses, got %d", i, len(ft.formula),
			p.AddedOriginalClauses())
	}
}

func TestFormulas(t *testing.T) {
	var p *Picosat
	var status int
	var solution []bool
	for i, ft := range formulaTests {
		p = NewPicosat(0)
		p.AddClauses(ft.formula)
		status, solution = p.Solve()
		wasExpected(t, i, p, &ft, status, solution)
		p.Delete()
	}
}

// Also cribbed from Pycosat
func TestPropLimit(t *testing.T) {
	var p *Picosat
	var status int
	var solution []bool
	ft := formulaTests[0]
	var limit uint64
	for limit = 1; limit < 20; limit++ {
		p = NewPicosat(limit)
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
	var a, b *Picosat
	b = NewPicosat(0)
	b.Delete()
	for name, p := range map[string]*Picosat{"uninit": a, "deleted": b} {
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
				name, status, solution)
		}
	}
}
