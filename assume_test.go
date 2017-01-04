// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import (
	"fmt"
	"reflect"
	"testing"
)

func TestLitArrayToSlice(t *testing.T) {
	// null pointers
	assertPanics(t, "litArrayToSlice", func() { litArrayToSlice(nil, 0) })
	assertPanics(t, "litArrayToSlice", func() { litArrayToSlice(nil, 1) })
	// not zero terminated
	badPtr := &cArray123[0]
	assertPanics(t, "litArrayToSlice", func() { litArrayToSlice(badPtr, 1) })
	assertPanics(t, "litArrayToSlice", func() { litArrayToSlice(badPtr, 2) })
	// zero length
	for maxLen := 0; maxLen <= 2; maxLen++ {
		if ls := litArrayToSlice(&cZero, 0); len(ls) != 0 {
			t.Errorf("Test 0-length litArrayToSlice, maxLen==%d: return value has length %d",
				maxLen, len(ls))
		}
	}
	// works correctly
	ptr := &cArray1230[0]
	expected := []Literal{1, 2, 3}
	for maxLen := 3; maxLen <= 10; maxLen++ {
		if ls := litArrayToSlice(ptr, maxLen); !reflect.DeepEqual(ls, expected) {
			t.Errorf("Test litArrayToSlice correct, maxLen==%d: expected %v but got %v",
				maxLen, expected, ls)
		}
	}
}

func TestAssumptionsSucceeding(t *testing.T) {
	successTests := []struct {
		assumpts  []Literal // The literals which should be assumed true/false
		solutions int       // The number of solutions that we expect to produce
	}{
		{[]Literal{1}, 10}, // We use formulaTests[0].formula below
		{[]Literal{2}, 9},
		{[]Literal{3}, 6},
		{[]Literal{4, 5}, 4},
	}

	for i, at := range successTests {
		t.Run(fmt.Sprintf("successTests[%d]", i), func(t *testing.T) {
			p, _ := New(nil)
			p.AddClauses(formulaTests[0].formula)

			count := 0
			for ; ; count++ {
				for _, lit := range at.assumpts {
					p.Assume(lit)
				}
				sol, status := p.Solve()
				if status != Satisfiable {
					break
				}

				// All the UNSAT methods should give zero answers.
				if p.FailedAssumption(at.assumpts[0]) {
					t.Errorf("FailedAssumption: expected %v not to be failed", at.assumpts[0])
				}
				if r := p.FailedAssumptions(); !reflect.DeepEqual(r, []Literal{}) {
					t.Errorf("FailedAssumptions: expected [], got %v", r)
				}

				p.BlockSolution(sol)
			}
			if count != at.solutions {
				t.Errorf("Expected %d solution(s) for assumptions %v; got %d",
					at.solutions, at.assumpts, count)
			}
		})
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
		t.Errorf("Expected failed assumptions %v != %v actual", failed, actual)
	}
	for _, f := range failed {
		if !p.FailedAssumption(f) {
			t.Errorf("Expected literal %v to be a failed assumption", f)
		}
	}

	i, wanted := 0, [][]Literal{{3, 5}, {3, 5}, {5, 4}, {}}
	for a := p.MaxSatisfiableAssumptions(); len(a) > 0; i++ {
		if !reflect.DeepEqual(a, wanted[i]) {
			t.Errorf("(Next)MaxSat'Assumpt's: Got %v wanted %v", a, wanted[i])
		}
		a = p.NextMaxSatisfiableAssumptions()
	}
	if a := p.MaxSatisfiableAssumptions(); !reflect.DeepEqual(a, []Literal{}) {
		t.Errorf("MaxSatisfiableAssumptions: CNF inconsistent, so wanted []Literal{}, but got %v", a)
	}
}

// TestCrashOnUnsatResetFailedAssumptions tests that if you reset the
// assumptions after Solve returns UNSAT then FailedAssumption(s) do not crash.
func TestCrashOnUnsatResetFailedAssumptions(t *testing.T) {
	ft := formulaTests[0]

	assertUnsat := func(p *Pigosat) {
		if r := p.Res(); r != Unsatisfiable {
			t.Fatalf("Expected %v, got %v", Unsatisfiable, r)
		}
	}

	run := func(name string, f func(*Pigosat)) {
		t.Run(name, func(t *testing.T) {
			p, _ := New(nil)
			p.AddClauses(ft.formula)
			p.Assume(3)
			p.Assume(4)
			p.Assume(5)
			p.Solve()

			assertUnsat(p)
			if !p.FailedAssumption(3) {
				t.Fatalf("Expected assumption '3' to fail")
			}
			assertUnsat(p)
			f(p)
			assertUnsat(p)
			// Either the next two assertions work or they crash with this message:
			//   *** picosat: API usage: expected to be in UNSAT state
			//   SIGABRT: abort
			if p.FailedAssumption(3) {
				t.Errorf("Did not expect assumption '3' to fail")
			}
			if r := p.FailedAssumptions(); len(r) != 0 {
				t.Errorf("Expected []Literal{}, got %v", r)
			}
		})
	}

	run("Assume", func(p *Pigosat) { p.Assume(3) })
	run("BlockSolution", func(p *Pigosat) {
		if err := p.BlockSolution(ft.expected); err != nil {
			t.Fatalf(err.Error())
		}
	})
	run("AddClauses-empty", func(p *Pigosat) { p.AddClauses(Formula{{3}}) })
	run("AddClauses-nil", func(p *Pigosat) { p.AddClauses(Formula{nil}) })
}

// TestNextMaxSatisfiableAssumptionsAsIterator tests that NextMaxSatisfiableAssumptions
// can be used as an iterator. In particular, this test panics if Solve calls
// BlockSolution when Solve returns Satisfiable.
func TestNextMaxSatisfiableAssumptionsAsIterator(t *testing.T) {
	var formula = Formula{{1, 2, 3}, {1, 2}, {2, 3}}
	p, _ := New(nil)
	p.AddClauses(formula)
	p.Assume(1)
	p.Assume(-2)
	p.Solve()
	p.Assume(-1)
	p.Assume(-2)
	ms := make([][]Literal, 0)
	for m := p.NextMaxSatisfiableAssumptions(); len(m) > 0; m = p.NextMaxSatisfiableAssumptions() {
		ms = append(ms, m)
	}
	expected := [][]Literal{{-1}, {-2}}
	if !reflect.DeepEqual(ms, expected) {
		t.Errorf("Expected %v. Got %v.", expected, ms)
	}
}

// ExamplePigosat_Assume demonstrates how to use Assume and related methods.
func ExamplePigosat_Assume() {
	var formula = Formula{{1, 2, 3}, {1, 2}, {2, 3}}
	p, _ := New(nil)
	p.AddClauses(formula)
	fmt.Println("Formula:", formula)
	solution, status := p.Solve()
	fmt.Println("No assumptions:", status, "solution ==", solution)

	// Satisfiable assumptions
	fmt.Println()
	fmt.Println("**** SATISFIABLE ASSUMPTIONS ****")
	p.Assume(1)
	p.Assume(-2)
	// Assumptions do not change the number of clauses.
	fmt.Println("Assume  1, -2 : Number of clauses:", p.AddedOriginalClauses())
	solution, status = p.Solve()
	fmt.Println("               ", status, "solution ==", solution)

	// Calls to p.AddClauses or p.Assume cancel assumptions 1 and -2
	// immediately, or a second call to p.Solve also cancels the assumptions.
	p.Assume(-3)
	solution, status = p.Solve()
	fmt.Println("Assume      -3:", status, "solution ==", solution)

	// Unsatisfiable assumptions
	fmt.Println()
	fmt.Println("**** UNSATISFIABLE ASSUMPTIONS ****")
	p.Assume(-1)                 // assume unit clause Clause{-1, 0}
	p.Assume(-2)                 // assume unit clause Clause{-2, 0}
	solution, status = p.Solve() // assumes -1 and -2 hold
	fmt.Println("Assume -1, -2 :", status, "solution ==", solution)
	// Assumptions -1 and -2 caused unsatisfiability.
	fmt.Println("                Failed assumptions:", p.FailedAssumptions())
	fmt.Println("                Assumption -1 failed:", p.FailedAssumption(-1))
	fmt.Println("                Assumption -2 failed:", p.FailedAssumption(-2))
	// Not every subset of the assumptions causes unsatisfiability.
	// p.MaxSatisfiableAssumptions would return the same as
	// p.NextMaxSatisfiableAssumptions, but the return value wouldn't change
	// with each call like it does with p.NextMaxSatisfiableAssumptions.
	fmt.Println("                Maximal satisfiable subset of assumptions 1:", p.NextMaxSatisfiableAssumptions())
	fmt.Println("                Maximal satisfiable subset of assumptions 2:", p.NextMaxSatisfiableAssumptions())
	fmt.Println("                Maximal satisfiable subset of assumptions 3:", p.NextMaxSatisfiableAssumptions())
	// p.NextMaxSatisfiableAssumptions does add clauses.
	fmt.Println("                Number of clauses:", p.AddedOriginalClauses())

	// Unknown status
	// Assumptions are valid but p.Solve returns no Solution assignment. The
	// solver knowns the status is Unknown until a call to p.Assume,
	// p.AddClauses, or p.Solve resets the assumptions.

	// Output:
	// Formula: [[1 2 3] [1 2] [2 3]]
	// No assumptions: Satisfiable solution == {1:true , 2:true , 3:true}
	//
	// **** SATISFIABLE ASSUMPTIONS ****
	// Assume  1, -2 : Number of clauses: 3
	//                 Satisfiable solution == {1:true , 2:false, 3:true}
	// Assume      -3: Satisfiable solution == {1:true , 2:true , 3:false}
	//
	// **** UNSATISFIABLE ASSUMPTIONS ****
	// Assume -1, -2 : Unsatisfiable solution == {}
	//                 Failed assumptions: [-1 -2]
	//                 Assumption -1 failed: true
	//                 Assumption -2 failed: true
	//                 Maximal satisfiable subset of assumptions 1: [-1]
	//                 Maximal satisfiable subset of assumptions 2: [-2]
	//                 Maximal satisfiable subset of assumptions 3: []
	//                 Number of clauses: 5
}
