(lang dune 3.11)
(name coq-quantumlib)
(version 1.8.0)
(using coq 0.3)
(warnings (deprecated_coq_lang_lt_08 disabled))

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
   (rocq (and (>= 9.0) (< 9.1)))))
