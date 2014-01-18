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

Building
--------

Go's [cgo](http://golang.org/cmd/cgo/) system claims to compile C source code it
finds, but I can't figure out how to get it to work. So you'll have to compile
PicoSAT first. You can simply compile picosat.c without anything else:

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

Contributing
------------

If you notice a bug or would like to request a feature, please file an [issue
ticket](https://github.com/wkschwartz/pigosat/issues), checking to see if one
exists already.

If you would like to contribute code, please
[fork](https://github.com/wkschwartz/PiGoSAT/fork) PiGoSAT and send a [pull
request](https://help.github.com/articles/using-pull-requests).