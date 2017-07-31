PiGoSAT
=======

Go (golang) bindings for Picosat, the satisfiability solver

Tested on Go versions 1.7 and 1.8, but may work on earlier versions of Go.

[![GoDoc](https://godoc.org/github.com/wkschwartz/pigosat/github?status.svg)](https://godoc.org/github.com/wkschwartz/pigosat)
[![Build Status](https://travis-ci.org/wkschwartz/pigosat.svg?branch=master)](https://travis-ci.org/wkschwartz/pigosat)
[![Coverage Status](https://coveralls.io/repos/github/wkschwartz/pigosat/badge.svg?branch=master)](https://coveralls.io/github/wkschwartz/pigosat?branch=master)
[![Go Report Card](https://goreportcard.com/badge/github.com/wkschwartz/pigosat)](https://goreportcard.com/report/github.com/wkschwartz/pigosat)

Downloading
-----------

The project is hosted on [GitHub](https://github.com/wkschwartz/pigosat). You
can either download a [release](https://github.com/wkschwartz/PiGoSAT/releases)
or use "go get":

```bash
$ go get github.com/wkschwartz/pigosat
```

PiGoSAT is a wrapper around [Picosat](http://fmv.jku.at/picosat/), whose C
source files are included in this repository.

Contributing
------------

If you notice a bug or would like to request a feature, please file an [issue
ticket](https://github.com/wkschwartz/pigosat/issues), checking to see if one
exists already.

If you would like to contribute code, please
[fork](https://github.com/wkschwartz/PiGoSAT/fork) PiGoSAT and send a [pull
request](https://help.github.com/articles/using-pull-requests).

### Updating PicoSAT

Replace `picsoat.h`, `picosat.c`, and update `PicosatVersion` in
`pigosat.go`. Copy `LICENSE` from PicoSAT to `LICENSE.picosat` in PiGoSAT.

### Other maintenance notes

Test PiGoSAT by switching to its source directory and running

```bash
$ go vet .
$ go test -race
```

Before committing, please run

```bash
$ gofmt -w -s
```

The only place you need to update the version number is in `pigosat.go`'s
`Version` constant. However, if you `git tag` or make a release on GitHub,
make sure the version number matches the tag name.

When a new major or minor version (x.0 or 1.x) of Go is available, increment the
versions you test PiGoSAT with in `.travis.yml`, and make a note at the top of
this README document. Go only supports the current and last minor versions
(e.g., 1.8 and 1.7) with security releases, so these are the versions that
PiGoSAT should support.
