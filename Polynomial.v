Require Import Psatz.
Require Import String.
Require Export Complex.
Require Export Matrix.
Require Import List.


(*
Require Export CoRN.fta.FTA. 
Require Export CoRN.coq_reals.Rreals_iso.
*)



Declare Scope poly_scope.
Delimit Scope poly_scope with P.
Open Scope poly_scope.

(* polynomial represented by a list of coeficients and a degree*)
Definition Polynomial (n : nat) := list (Complex.C).


Definition WF_Poly {n : nat} (p : Polynomial n) :=
  length p = (S n).

Definition eval_P {n : nat} (p : Polynomial n) (x : Complex.C):=
  Csum (fun i => (nth i p C0)* x^i) (S n).



Definition Pplus {n} (p1 p2 : Polynomial n) : Polynomial n := zipWith Cplus p1 p2.
Definition Pscale {n} (c : C) (p1 : Polynomial n) : Polynomial n := map (Cmult c) p1.



Infix "+," := Pplus (at level 40, left associativity) : poly_scope. 
Infix "*," := Pscale (at level 40, left associativity) : poly_scope.
Notation "P [[ x ]]" := (eval_P P x) (at level 0) : poly_scope.  

Axiom Pplus_eval : forall {n} (p1 p2 : Polynomial n) (c : C),
  (p1 +, p2)[[c]] = p1[[c]] + p2[[c]].

Axiom Pscale_eval : forall {n} (p1 : Polynomial n) (c1 c2 : C),
  (c1 *, p1)[[c2]] = c1 * p1[[c2]].


(*****************************************************)
(* First, we show that our C is the same as ccorns C *)
(*****************************************************)



(*

Definition CtoCC (c : Complex.C) : CC_set := Build_CC_set (RasIR (fst c)) (RasIR (snd c)). 
Definition CCtoC (c : CC_set) : Complex.C := (IRasR (Re c), IRasR (Im c)).


Lemma CasCCasC_id : forall (x : Complex.C), (CCtoC (CtoCC x) = x).
Proof. intros.
       unfold CtoCC, CCtoC.
       simpl.
       do 2 rewrite RasIRasR_id.
       rewrite surjective_pairing.
       easy. 
Qed.


(*
Lemma CCasCasCC_id : forall (x : CC_set), (CtoCC (CCtoC x) = x).
Proof. intros.
       unfold CtoCC, CCtoC.
       simpl.
       do 2 rewrite RasIRasR_id.
       rewrite surjective_pairing.
       easy. 
Qed. *)

*)
       

Theorem Fundamental_Theorem_Algebra : forall {n : nat} (p : Polynomial n),
  (n > 0)%nat -> (exists c : C, p[[c]] = C0).
Proof. Admitted.

