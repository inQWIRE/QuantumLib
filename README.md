# QuantumLib

[![CI](https://github.com/inQWIRE/QuantumLib/actions/workflows/coq-action.yml/badge.svg)](https://github.com/inQWIRE/QuantumLib/actions/workflows/coq-action.yml)

QuantumLib is a Coq library for reasoning about quantum programs. It was co-developed with (and is used in) several other projects in inQWIRE including [QWIRE](https://github.com/inQWIRE/QWIRE), [SQIR](https://github.com/inQWIRE/SQIR), and [VyZX](https://github.com/inQWIRE/VyZX).

## Compilation

Tested with Coq versions 8.12 -- 8.15.

To compile run `make all`.

**TODO: add instructions for installing with opam**

## Documentation

Run `make doc` to generate documentation.

**TODO: host generated documentation on a GitHub page**

## Directory Contents

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
