CoqQFBV
=======

CoqQFBV is a certified SMT QF_BV solver. It accepts SMT QF_BV queries in the
[SMTLIB2](http://smtlib.cs.uiowa.edu) format. Given an SMTLIB2 file, CoqQFBV
first converts the assertions in the file into a formal QF_BV expression.
A CNF formula (stored in the DIMACS format) is then constructed from the
formal QF_BV expression by a certified bit-blasting procedure. The SAT solver
[kissat](http://fmv.jku.at/kissat/) is invoked to solve the CNF formula.
If the result is unsat with a certificate, CoqQFBV verifies the certificate
using the certified SAT solver certificate checking tool chain
[GRAT](https://www21.in.tum.de/~lammich/grat/). If the result is sat with
assignments, CoqQFBV converts the CNF assignments back to SMT assignments
and verifies whether the SMT assignments satisfy the QF_BV expression using
a certified procedure.

The Coq source code in the directory src contains a formalization of a
bit-blasting procedure and its correctness proof. With the code extraction
mechanism of Coq, the certified OCaml code is extracted in
src/ocaml/extraction and is used by the certified SMT QF_BV solver in
src/ocaml.


Installation
============

To compile the formalization of the certified bit-blasting procedure in
CoqQFBV, the following packages are required.

* [Coq](https://coq.inria.fr) 8.11.0
* [MathComp](https://github.com/math-comp/math-comp) 1.10.0

To compile the certified SMT QF_BV solver of CoqQFBV, the following packages
are required.

* [OCaml](https://ocaml.org) 4.08.1
* [Dune](https://dune.build) 2.1.3 (or newer versions)
* [Zarith](https://github.com/ocaml/Zarith) 1.9.1 (or newer versions)

To run CoqQFBV, the following tools are required.

* [kissat](http://fmv.jku.at/kissat/)
* [gratgen](https://www21.in.tum.de/~lammich/grat/) and
  [gratchk](https://www21.in.tum.de/~lammich/grat/)

Make sure that the tools are installed and can be found in the PATH
environment variable.


On Ubuntu
---------

On Ubuntu 20.04 LTS, the packages for compilation can be installed by the
following command.

    $ sudo apt install ocaml ocaml-dune libzarith-ocaml-dev coq libssreflect-coq

The script setup-ubuntu can be used to install all required packages
and external tools on Ubuntu 20.04.


With OPAM
---------

The packages for compilation can also be installed via
[opam](http://opam.ocaml.org).

    $ opam switch create ocaml-base-compiler.4.08.1
    $ eval `opam env`
    $ opam repo add coq-released https://coq.inria.fr/opam/released
    $ opam install dune zarith
    $ opam pin coq 8.11.0
    $ opam pin coq-mathcomp-ssreflect 1.10.0
    $ opam install coq-mathcomp-algebra

Some system dependencies such as libgmp-dev on Ubuntu 20.04 may need to be
installed before installing opam packages.

Compilation
-----------

Run the following commands in the root directory of the CoqQFBV project to
compile the Coq formalization of the certified bit-blasting procedure.

    $ git submodule init
    $ git submodule update
    $ make -C lib/coq-nbits
    $ make -C lib/coq-ssrlib
    $ make

Run the following command in the directory src/ocaml to compile the
certified SMT QF_BV solver of CoqQFBV.

    $ dune build

The binary of CoqQFBV can be found in src/ocaml/_build/default.


Usage
=====

Assume the current directory is src/ocaml. To check the satisfiability of
a QF_BV query in an SMTLIB2 file query.smt2, run the following command.

    $ _build/default/coqQFBV.exe query.smt2

For large QF_BV queries, CoqQFBV runs faster with more memory allocated,
which can be adjusted by the OCAMLRUNPARAM environment variable.
For example, the following command may have better performance in answering
large queries.

    $ OCAMLRUNPARAM="s=2G" _build/default/coqQFBV.exe query.smt2

For QF_BV queries with a lot of conjunctions, it is better to run CoqQFBV
with the argument -split-conjs. For example,

    $ OCAMLRUNPARAM="s=2G" _build/default/coqQFBV.exe -split-conjs query.smt2

To see more available arguments, run the following command.

    $ _build/default/coqQFBV.exe -help
