// Copyright William Schwartz 2014. See the LICENSE file for more information.

package pigosat

type vertex uint
type graph struct {
	neighbors [][]vertex
}

// The Petersen graph
var petersen = graph{neighbors: [][]vertex{0: {1, 4, 5}, 1: {2, 0, 6}, 2: {1, 3, 7},
	3: {2, 4, 8}, 4: {0, 3, 9}, 5: {0, 7, 8}, 6: {1, 8, 9}, 7: {2, 5, 9},
	8: {3, 5, 6}, 9: {4, 6, 7}}}

func init() {
	for _, vertex := range petersen.Vertices() {
		if petersen.Degree(vertex) != 3 {
			panic("no!")
		}
	}
}

// NumVertices returns the number of vertices in graph g.
func (g *graph) NumVertices() uint {
	return uint(len(g.neighbors))
}

// Vertices returns a slice of vertex identifiers in graph g.
func (g *graph) Vertices() []vertex {
	v := make([]vertex, g.NumVertices())
	for i := 0; uint(i) < g.NumVertices(); i++ {
		v[i] = vertex(i)
	}
	return v
}

// Degree returns the degree of vertex v in graph g.
func (g *graph) Degree(v vertex) uint {
	if uint(v) < g.NumVertices() {
		return uint(len(g.neighbors[v]))
	}
	return 0
}

// Neighbors returns a slice of vertex v's neighbors or nil if v is not in g.
func (g *graph) Neighbors(v vertex) []vertex {
	if uint(v) < g.NumVertices() {
		return g.neighbors[v]
	}
	return nil
}

type color uint
type record struct {
		color color
		solution Solution
		status Status
	}
type coloring struct {
	g graph
	k color
	// For Minimizer interface
	records []record
}

// Var returns the variable identifier for coloring vertex v with color i. Zero
// if invalid. Colors can be 0 <= i < c.k.
func (c *coloring) Var(v vertex, i color) uint {
	if uint(v) >= c.g.NumVertices() || i >= c.k {
		return 0
	}
	return uint(color(v) * c.k + i + 1)
}

// VertexColor returns the vertex and color for which id is the variable
// identifier.
func (c *coloring) VertexColor(id uint) (vertex, color) {
	return vertex((id - 1) / uint(c.k)), color((id - 1) % uint(c.k))
}

// Colors returns a slice of all possible colors 0 <= i < c.k.
func (c *coloring) Colors() []color {
	v := make([]vertex, c.k)
	for i := 0; i < c.k; i++ {
		v[i] = i
	}
	return v
}

// Formula returns a conjuctive-normal-form formula for coloring the Petersen
// graph with k colors.
func (c *coloring) Formula(k uint) Formula {
	f := make(Formula)
	// Each vertex gets different colors
	for _, v := range c.g.Vertices() {
		for _, u := range c.g.Neighbors(v) {
			if u < v { // Avoid redundant clauses in undirected graphs.
				for _, color := range c.Colors() {
					f = append(f, Clause{-c.Var(v, color), -c.Var(u, color), 0})
				}
			}
		}
	}
	// Every vertex gets at least one color
	for v := range c.g.Vertices() {
		clause := make(Clause, c.k + 1)
		for _, color := range c.Colors() {
			clause = append(clause, c.Var(v, color))
		}
		f = append(f, append(clause, 0))
	}
	return f
}

// The Minimizer interface

func (c *coloring) LowerBound() int { return 1 }

func (c *coloring) UpperBound() int {
	maxDegree := 0
	for v := range c.g.Vertices() {
		if d := c.g.Degree(v); d > maxDegree {
			maxDegree = d
		}
	}
	return maxDegree
}

func (c *coloring) RecordSolution(color int, solution Solution, status Status) {
	if c.records == nil {
		c.records = make([]record)
	}
	c.records = append(c.records, record{color, solution, status})
}

func (c *coloring) IsFeasible(color int) (solution Solution, status Status) {
	p := New(nil)
}
