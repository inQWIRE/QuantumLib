(lang dune 2.8)
(name coq-quantumlib)
(version 1.6.0)
(using coq 0.2)

(generate_opam_files true)

(license MIT)
(authors "inQWIRE")
(maintainers "inQWIRE Developers")
(source (github inQWIRE/QuantumLib))
(documentation "https://inqwire.github.io/QuantumLib/toc.html")

(package
 (name coq-quantumlib)
 (synopsis "Coq library for reasoning about quantum programs")
 (description "\| inQWIRE's QuantumLib is a Coq library for reasoning
              "\|  about quantum computation and quantum programs.
 )
 (depends
   (coq (and (>= 8.16) (< 8.20)))))
