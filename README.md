# QuantumLib

QuantumLib was co-developed with several other projects in inQWIRE, including [QWIRE](https://github.com/inQWIRE/QWIRE), [SQIR](https://github.com/inQWIRE/SQIR), and [VyZX](https://github.com/inQWIRE/VyZX).

## Compilation

Requires Coq version 8.12-8.14 and the CoRN package.

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
opam install coq-corn
```

To compile run `make all`.

## Directory Contents

**TODO** Improve summaries.
* Complex.v - definition of Complex numbers, extending Coquelicot
* Eigenvectors.v
* Matrix.v - definition of matrices of complex numbers, associated lemmas and automation
* Measurement.v - useful predicates for describing the result of measurement
* Pad.v - definition of "pad" functions to extend a matrix to a larger space - useful for describing quantum gates
* Permutation.v - facts about permutation matrices
* Polynomial.v
* Prelim.v - some utility definitions and proofs
* Proportional.v - definition of equality up to a global phase
* Quantum.v - definitions of and proofs about common matrices used in quantum computing
* RealAux.v - supplement to Coq's axiomatized Reals
* VecSet.v
* VectorStates.v - abstractions for reasoning about quantum states as vectors