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
* Ctopology.v - a topology of open/closed sets is defined for the complex numbers, with lemmas about compactness
* Eigenvectors.v - a continuation of VecSet.v, this file contains more linear algebra that is sort of specific to quantum 
* FTA.v - this file is mostly just a messy proof of the fundamental theorem of algebra
* Matrix.v - definition of matrices of complex numbers, associated lemmas and automation
* Measurement.v - useful predicates for describing the result of measurement
* Pad.v - definition of "pad" functions to extend a matrix to a larger space
* Permutations.v - facts about permutation matrices
* Polar.v - defining polar complex numbers and showing that they are isomorphic to rectangular complex numbers
* Polynomial.v - definition of polynomials and corresponding lemmas
* Prelim.v - utility definitions and proofs
* Proportional.v - definition of equality up to a global phase
* Quantum.v - definitions of and proofs about common matrices used in quantum computing
* RealAux.v - supplement to Coq's axiomatized Reals
* VecSet.v - more advanced linear algebra definitions such as linear_independence, invertible, etc... and corresponding lemmas
* VectorStates.v - abstractions for reasoning about quantum states as vectors
