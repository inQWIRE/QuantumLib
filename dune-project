(lang dune 2.8)
(name coq-quantumlib)
(version 1.0.0)
(using coq 0.2)

(generate_opam_files true)

(source (github inQWIRE/QuantumLib))
(license MIT)
(authors "inQWIRE")
(maintainers "The inQWIRE Team")

(package
 (name coq-quantumlib)
 (synopsis "Coq library for reasoning about quantum programs")
 (description "\| inQWIRE's QuantumLib is a Coq library for reasoning
              "\|  about quantum programs.
 )
 (depends
   (coq (>= 8.12))))
