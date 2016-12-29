// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import (
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
	var status Status
	var sol Solution

	for _, at := range successTests {
		p, _ := New(nil)
		p.AddClauses(formulaTests[0].formula)

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
}
