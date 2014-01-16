package pigosat

import "testing"

// abs takes the absolute value of an int32 and casts it to int.
func abs(x int32) int {
	if x < 0 {
		return int(-x)
	}
	return int(x)
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
