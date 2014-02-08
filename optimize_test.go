package pigosat

import "testing"

// TestMinimize will test optimal values from `from` to `to`.
const (
	from = -32
	to = -from
)


func init() {
	if from >= to {
		panic("from >= to")
	}
}

type parameters struct {
	lower, upper, optimal int
}

type arguments struct {
	k, status int
	solution []bool
}

type minimizer struct {
	t *testing.T
	args chan arguments
	params parameters
}

func newMinimizer(lo, hi, opt int, t *testing.T) *minimizer {
	m := &minimizer{params: parameters{lower: lo, upper: hi, optimal: opt}, t: t}
	// A little testing by hand suggests 2 is faster than 0 or (to - from)
	m.args = make(chan arguments, 2)
	return m
}

func (m *minimizer) LowerBound() int { return m.params.lower }

func (m *minimizer) UpperBound() int { return m.params.upper }

func (m *minimizer) IsFeasible(k int) (status int, solution []bool) {
	if k < from {
		m.t.Errorf("k too low: %d", k)
	}
	if k > to {
		m.t.Errorf("k too hi: %d", k)
	}
	status = Satisfiable
	if k < m.params.optimal {
		status = Unsatisfiable
	}
	m.args <- arguments{k, status, solution}
	return
}

func (m *minimizer) RecordSolution(k, status int, solution []bool) {
	m.args <- arguments{k, status, solution}
}

// Check that RecordSolution is called with IsFeasible's output every time.
func checkFeasibleRecord(t *testing.T, v parameters, args <-chan arguments) {
	var last arguments
	count := 0
	for arg := range args {
		// Each call to IsFeasible is paried with a go RecordSolution. Thus
		// we're looking for pairs of arguments.
		if count % 2 == 0 {
			if arg.status == NotReady { // sentinel
				return
			}
			last = arg
			continue
		}
		if arg.k != last.k || arg.status != last.status ||
			!equal(arg.solution, last.solution) {
			t.Errorf("%+v: feasible=%+v record=%+v", v, last, arg)
		}
	}
}

// TestMinimize tests that the bisection search that Minimize does correctly
// finds the optimal value within the lower and upper bounds, that optimal and
// feasible flags are set correctly, Minimizer.RecordSolution is always called
// after Minimizer.IsFeasible.
func TestMinimize(t *testing.T) {
	for hi := from; hi <= to; hi++ {
		for lo := from; lo <= hi; lo++ {
			for opt := lo; opt <= hi + 1; opt++ {
				m := newMinimizer(lo, hi, opt, t)
				go checkFeasibleRecord(t, m.params, m.args)
				min, optimal, feasible := Minimize(m)
				m.args <- arguments{status: NotReady} // sentinel
				if opt <= hi && min != opt {
					t.Errorf("%+v: min=%d", m.params, min)
				}
				if opt > lo && opt <= hi && !optimal {
					t.Errorf("%+v: Should have been optimal", m.params)
				} else if opt <= lo && optimal {
					t.Errorf("%+v: Should not have been optimal", m.params)
				}
				if opt <= hi && !feasible {
					t.Errorf("%+v: Should have been feasible", m.params)
				} else if opt > hi && feasible {
					t.Error("%+v: Should not have been feasible", m.params)
				}
			} // opt
		} // lo
	} // hi
} // func
