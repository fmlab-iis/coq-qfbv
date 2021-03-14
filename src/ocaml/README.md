CoqQFBV
=======

CoqQFBV is a certified solver for SMT QFBV theory.
It accepts SMT QFBV queries in the [SMTLIB2](http://smtlib.cs.uiowa.edu)
format.

Installation
============

To compile CoqQFBV, the following packages are required.

* [OCaml](https://ocaml.org) 4.08.1
* [Dune](https://dune.build) 2.1.3 (or newer versions)
* [Zarith](https://github.com/ocaml/Zarith) 1.9.1 (or newer versions)

On Ubuntu 20.04 LTS, these packages can be installed by the following command.

    $ sudo apt-get install ocaml ocaml-dune libzarith-ocaml-dev

The packages can also be installed via [opam](http://opam.ocaml.org).

    $ opam switch create ocaml-base-compiler.4.08.1
    $ eval `opam env`
    $ opam install dune zarith

Once the packages are installed, run the following command to compile CoqQFBV.

    $ dune build

The binary of CoqQFBV can be found in _build/default.

Usage
=====

To run CoqQFBV, the following tools are required.

* [kissat](http://fmv.jku.at/kissat/)
* [gratgen](https://www21.in.tum.de/~lammich/grat/) and
  [gratchk](https://www21.in.tum.de/~lammich/grat/)

Make sure that the tools are installed and can be found in the PATH
environment variable.
To check the satisfiability of a QFBV query in an SMTLIB2 file query.smt2,
run the following command.

    $ _build/default/coqQFBV.exe query.smt2

For large QFBV queries, CoqQFBV runs faster with more memory allocated,
which can be adjusted by the OCAMLRUNPARAM environment variable.
For example, the following command may have better performance in answering
large queries.

    $ OCAMLRUNPARAM="s=2G" _build/default/coqQFBV.exe query.smt2
