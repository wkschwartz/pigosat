// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

import (
	"fmt"
)

// Type Minimizer allows you to find the lowest integer K such that
//    LowerBound() <= K <= UpperBound()
// and IsFeasible(K) returns status Satisfiable.
type Minimizer interface {
	// LowerBound returns a lower bound for the optimal value of k.
	LowerBound() int

	// UpperBound returns an upper bound for the optimal value of k.
	UpperBound() int

	// IsFeasible takes a value k and returns whether the Minimizer instance's
	// underlying model is feasible for that input value. IsFeasible can model
	// any set of constraints it likes as long as there is a unique integer K
	// such that k < K implies IsFeasible(k) returns status Unsatisfiable and
	// k >= K implies IsFeasible(k) returns status Satisfiable.
	IsFeasible(k int) (status Status, solution Solution)

	// RecordSolution allows types implementing this interface to store
	// solutions for after minimization has finished. Must be safe for parallel
	// use.
	RecordSolution(k int, status Status, solution Solution)
}

// Minimize finds the value min that minimizes Minimizer m. If the value can be
// proved to be optimal, that is, k < min causes m.IsFeasible(k) to return
// status Unsatisfiable, optimal will be set to true. If
// m.IsFeasible(m.UpperBound()) returns status Unsatisfiable, feasible will be
// set to false. Every return value from IsFeasible will be passed to
// m.RecordSolution in a separate goroutine. Panic if m.UpperBound() <
// m.LowerBound(). If m.IsFeasible returns a status other than Satisfiable, it
// will be treated as Unsatisfiable.
func Minimize(m Minimizer) (min int, optimal, feasible bool) {
	hi, lo := m.UpperBound(), m.LowerBound()
	if hi < lo {
		panic(fmt.Errorf("UpperBound()=%d < LowerBound()=%d", hi, lo))
	}
	status, solution := m.IsFeasible(hi)
	go m.RecordSolution(hi, status, solution)
	if status != Satisfiable {
		return hi, false, false
	}
	for hi > lo {
		k := lo + (hi-lo)/2 // avoid overfow. See sort/search.go in stdlib
		status, solution = m.IsFeasible(k)
		go m.RecordSolution(k, status, solution)
		if status == Satisfiable {
			hi = k
		} else {
			lo = k + 1
			optimal = true
		}
	}
	return hi, optimal, true
}
