Require Import Psatz.
Require Import String.
Require Import Program.
Require Export Complex.
Require Export Matrix.
Require Import List.


(* polynomial represented by a list of coeficients and a degree*)
Definition Polynomial (n : nat) := list C.


Definition WF_Poly {n : nat} (p : Polynomial n) :=
  length p = (S n).

Definition eval_P (n : nat) (p : Polynomial n) (x : C):=
  Csum (fun i => (nth i p C0)* x^i) (S n).


Lemma test1 :
  eval_P 2 [C2; C1; Ci] C2 = (4, 4).
Proof. unfold eval_P. simpl. lca. Qed.





Theorem Fundamental_Theorem_Algebra : forall {n : nat} (p : Polynomial n),
  (n > 0)%nat -> (exists c : C, eval_P n p c = C0).
Proof. Admitted.

