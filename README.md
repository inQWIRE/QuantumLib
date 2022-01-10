# QuantumLib

[![CI](https://github.com/inQWIRE/QuantumLib/actions/workflows/coq-action.yml/badge.svg)](https://github.com/inQWIRE/QuantumLib/actions/workflows/coq-action.yml)

QuantumLib is a Coq library for reasoning about quantum programs. It was co-developed with (and is used in) several other projects in inQWIRE including [QWIRE](https://github.com/inQWIRE/QWIRE), [SQIR](https://github.com/inQWIRE/SQIR), and [VyZX](https://github.com/inQWIRE/VyZX).

## Compilation

Tested with Coq versions 8.12 -- 8.14.

To compile run `make all`.

**TODO: add instructions for installing with opam**

## Documentation

Run `make doc` to generate documentation.

**TODO: host generated documentation on a GitHub page**

## Directory Contents

**TODO: Improve summaries. (Or remove entirely if the coqdoc documentation is sufficient.)**

* Complex.v - definition of Complex numbers, extending [Coquelicot](http://coquelicot.saclay.inria.fr/)'s
* Ctopology.v
* Eigenvectors.v
* FTA.v
* Matrix.v - definition of matrices of complex numbers, associated lemmas and automation
* Measurement.v - useful predicates for describing the result of measurement
* Pad.v - definition of "pad" functions to extend a matrix to a larger space
* Permutations.v - facts about permutation matrices
* Polar.v
* Polynomial.v
* Prelim.v - utility definitions and proofs
* Proportional.v - definition of equality up to a global phase
* Quantum.v - definitions of and proofs about common matrices used in quantum computing
* RealAux.v - supplement to Coq's axiomatized Reals
* VecSet.v
* VectorStates.v - abstractions for reasoning about quantum states as vectors
