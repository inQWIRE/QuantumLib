# QuantumLib

[![CI](https://github.com/inQWIRE/QuantumLib/actions/workflows/coq-action.yml/badge.svg)](https://github.com/inQWIRE/QuantumLib/actions/workflows/coq-action.yml)
[![coqdoc][coqdoc-shield]][coqdoc-link]

[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://inqwire.github.io/QuantumLib/toc.html

QuantumLib is a Coq library for reasoning about quantum programs. It was co-developed with (and is used in) several other projects in inQWIRE including [QWIRE](https://github.com/inQWIRE/QWIRE), [SQIR](https://github.com/inQWIRE/SQIR), and [VyZX](https://github.com/inQWIRE/VyZX).

## Compilation

Tested with Coq versions 8.12 -- 8.15.
Experimental on 8.16

This project requires `opam` & `dune` to be installed.

Install `dune` using `opam install dune`

To compile run `make all`.

Stable versions of QuantumLib may be installed using `opam install coq-quantumlib`

## Using With Other Projects

### Official Release

To install the official release of QuantumLib, run the following.
```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-quantumlib
```

### Dev

To install the development version of QuantumLib, run `opam pin coq-quantumlib https://github.com/inQWIRE/QuantumLib.git`. This should allow you to import QuantumLib files into other Coq files. To pull subsequent updates, run `opam install coq-quantumlib`. When importing/exporting specific files, refer to QuantumLib files as `QuantumLib.FILENAME`.

## Directory Contents

Auto-generated documentation is available at https://inqwire.github.io/QuantumLib/toc.html.

* Complex.v - Definition of Complex numbers, extending [Coquelicot](http://coquelicot.saclay.inria.fr/)'s.
* Ctopology.v - A topology of open/closed sets is defined for the complex numbers, with lemmas about compactness.
* DiscreteProb.v - Theory of discrete probability distributions and utility to describe running a quantum program ("apply_u") and sampling from the output distribution.
* Eigenvectors.v - A continuation of VecSet.v, this file contains more linear algebra that is sort of specific to quantum.
* FTA.v - This file is mostly just a messy proof of the fundamental theorem of algebra.
* Matrix.v - Definition of matrices of complex numbers, associated lemmas and automation.
* Measurement.v - Useful predicates for describing the result of measurement.
* Pad.v - Definition of "pad" function to extend a matrix to a larger space.
* Permutations.v - Facts about permutation matrices.
* Polar.v - Defining polar complex numbers and showing that they are isomorphic to rectangular complex numbers.
* Polynomial.v - Definition of polynomials and corresponding lemmas.
* Prelim.v - Basic utility definitions and proofs.
* Proportional.v - Definition of equality up to a global phase.
* Quantum.v - Definitions of and proofs about common matrices used in quantum computing.
* RealAux.v - Supplement to Coq's axiomatized Reals.
* VecSet.v - More advanced linear algebra definitions such as linear independence, invertability, etc. and corresponding lemmas.
* VectorStates.v - Abstractions for reasoning about quantum states as vectors.
