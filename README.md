PiGoSAT
=======

Go (golang) bindings for Picosat, the satisfiability solver

Downloading
-----------

The project is hosted on [GitHub](https://github.com/wkschwartz/pigosat). You
can either download a [release](https://github.com/wkschwartz/PiGoSAT/releases)
or use Git:

```bash
$ git clone https://github.com/wkschwartz/pigosat
```

Building and Installation
-------------------------

PiGoSAT is a wrapper around [Picosat](http://fmv.jku.at/picosat/), whose C
source files are included in this repository. Go's
[cgo](http://golang.org/cmd/cgo/) system claims to compile C source code it
finds, but I can't figure out how to get it to work. So you'll have to compile
PicoSAT first. For this reason, PiGoSAT is not `go get`able. You can simply
compile picosat.c without anything else:

```bash
$ cd picosat
$ gcc -Wall -Wextra -DNDEBUG -O3 -c picosat.c
$ cd ..
```

After that the `go command` works as usual. The following incantation runs the
tests and if they pass, installs PiGoSAT. (Ensure your
[GOPATH](http://golang.org/cmd/go/#hdr-GOPATH_environment_variable) is set.)

```bash
$ go test && go install
```

Use
---

After completing the building and installation steps above, importation should
work as usual. Create a `Pigosat` object `p` and use its methods. Because of the
C-language PicoSAT component of PiGoSAT, you must explicitly free `p` when you
are done using `p`, and you will not be able to use `p` thereafter. The best
practice if you are using `p` all within one function is to use `defer`.

Designing your model is beyond the scope of this document, but Googling
"satisfiability problem", "conjunctive normal form", and "DIMACS" are good
places to start. Once you have your model, number its variables from 1 to
_n_. Construct clauses as slices of `int32`s giving the index of each
variable. Negate each variable's index if the model's literal is negated. Add
the clauses with `Pigosat.AddClauses`. Solve the formula with
`Pigosat.Solve`. See each method's godoc comment for more information.


```go
package main
import "pigosat"
func main() {
	p := pigosat.NewPigosat(0)
	defer p.Delete()
	p.AddClauses([][]int32{{1, 2}, {-2}})
	status, solution := p.Solve()
	// Now status should equal pigosat.Satisfiable and solution should be
	// such that solution[1] == true and solution[2] == false. solution[0]
	// is always ignored.
}
```


Contributing
------------

If you notice a bug or would like to request a feature, please file an [issue
ticket](https://github.com/wkschwartz/pigosat/issues), checking to see if one
exists already.

If you would like to contribute code, please
[fork](https://github.com/wkschwartz/PiGoSAT/fork) PiGoSAT and send a [pull
request](https://help.github.com/articles/using-pull-requests).