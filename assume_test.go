// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import (
	"fmt"
	"reflect"
	"testing"
)

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
		p, _ := New(nil)
		p.AddClauses(formulaTests[0].formula)

		count := 0
		for ; ; count++ {
			for _, lit := range at.assumpts {
				p.Assume(lit)
			}
			status, sol := p.Solve()
			if status != Satisfiable {
				break
			}

			// All the UNSAT methods should give zero answers.
			if p.FailedAssumption(at.assumpts[0]) {
				t.Errorf("Test %d: FailedAssumption: expected %v not to be failed", i, at.assumpts[0])
			}
			if r := p.FailedAssumptions(); !reflect.DeepEqual(r, []Literal{}) {
				t.Errorf("Test %d: FailedAssumptions: expected [], got %v", i, r)
			}

			p.BlockSolution(sol)
		}
		if count != at.solutions {
			t.Errorf("Test %d: Expected %d solution(s) for assumptions %v; got %d",
				i, at.solutions, at.assumpts, count)
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

// TestAssumptionsNoCrash tests that where Picosat crashes when using the
// *assumption* methods when the solver's state is not UNSAT, Pigosat should
// just give a simple zero answer.
func TestAssumptionsNoCrash(t *testing.T) {
	p, _ := New(nil)
	p.AddClauses(formulaTests[0].formula)
	p.Assume(3)
	p.Assume(4)
	p.Assume(5)
	p.Solve()

	if r := p.Res(); r != Unsatisfiable {
		t.Fatalf("Expected %v, got %v", Unsatisfiable, r)
	}
	if !p.FailedAssumption(3) {
		t.Fatalf("Expected literal 3 to be a failed assumption")
	}
	if r := p.Res(); r != Unsatisfiable {
		t.Fatalf("Expected %v, got %v", Unsatisfiable, r)
	}

	p.Assume(3)
	if r := p.Res(); r != Unsatisfiable {
		t.Fatalf("Expected %v, got %v", Unsatisfiable, r)
	}

	if p.FailedAssumption(3) {
		t.Errorf("FailedAssumption: Expected false, got true")
	}
	if r := p.FailedAssumptions(); len(r) != 0 {
		t.Errorf("FailedAssumptions: Expected []Literal{}, got %v", r)
	}
}

// ExampleAssume demonstrates how to use Assume and related methods.
func ExamplePigosat_Assume() {
	var formula = Formula{{1, 2, 3}, {1, 2}, {2, 3}}
	p, _ := New(nil)
	p.AddClauses(formula)
	fmt.Println("Formula:", formula)
	status, solution := p.Solve()
	fmt.Println("No assumptions:", status, "solution ==", solution)

	// Satisfiable assumptions
	fmt.Println()
	fmt.Println("**** SATISFIABLE ASSUMPTIONS ****")
	p.Assume(1)
	p.Assume(-2)
	// Assumptions do not change the number of clauses.
	fmt.Println("Assume  1, -2 : Number of clauses:", p.AddedOriginalClauses())
	status, solution = p.Solve()
	fmt.Println("               ", status, "solution ==", solution)

	// Calls to p.AddClauses or p.Assume cancel assumptions 1 and -2
	// immediately, or a second call to p.Solve also cancels the assumptions.
	p.Assume(-3)
	status, solution = p.Solve()
	fmt.Println("Assume      -3:", status, "solution ==", solution)

	// Unsatisfiable assumptions
	fmt.Println()
	fmt.Println("**** UNSATISFIABLE ASSUMPTIONS ****")
	p.Assume(-1)                 // assume unit clause Clause{-1, 0}
	p.Assume(-2)                 // assume unit clause Clause{-2, 0}
	status, solution = p.Solve() // assumes -1 and -2 hold
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

	// **** SATISFIABLE ASSUMPTIONS ****
	// Assume  1, -2 : Number of clauses: 3
	//                 Satisfiable solution == {1:true , 2:false, 3:true}
	// Assume      -3: Satisfiable solution == {1:true , 2:true , 3:false}

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
