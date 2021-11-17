Require Export Polynomial.

(************************************)
(* First, we define a topology on C *)
(************************************)

Declare Scope topology_scope.
Delimit Scope topology_scope with T.
Open Scope topology_scope.


(* we define a subset of C as a function from C to {True, False} *)
(* so c is in A if A(c) = True *)
Definition Csubset := C -> Prop.

Definition union (A B : Csubset) : Csubset :=
  fun c => A c \/ B c.

Definition intersection (A B : Csubset) : Csubset :=
  fun c => A c /\ B c.

Definition complement (A : Csubset) : Csubset :=
  fun c => not (A c).

Definition is_in (a : C) (A : Csubset) : Prop := A a.

Definition subset (A B : Csubset) : Prop :=
  forall c, is_in c A -> is_in c B.

Definition ϵ_disk (a : C) (ϵ : R) : Csubset :=
  fun c => Cmod (a - c) < ϵ.


Infix "∪" := union (at level 50, left associativity) : topology_scope.
Infix "∩" := intersection (at level 40, left associativity) : topology_scope.
Infix "⊂" := subset (at level 0) : topology_scope.
Notation "A *" := (complement A) (at level 0) : topology_scope.
Infix "∈" := is_in (at level 0) : topology_scope.
Notation "B( a , ϵ )" := (ϵ_disk a ϵ) (at level 30, no associativity) : topology_scope.


Definition open (A : Csubset) : Prop :=
  forall c, c ∈ A -> exists ϵ, ϵ > 0 /\ B(c,ϵ) ⊂ A.

Definition closed (A : Csubset) : Prop :=
  open (A*).




Lemma poly_min : forall (p : Polynomial), 
  exists m, (forall c, Cmod p[[m]] <= Cmod p[[c]]).
Proof. Admitted.


(******************)
(* Must prove FTA *)
(******************)
 

Theorem Fundamental_Theorem_Algebra : forall (p : Polynomial),
  (Polynomial.degree p > 0)%nat -> (exists c : Complex.C, p[[c]] = C0).
Proof. Admitted. 
