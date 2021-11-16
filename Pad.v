Require Import Psatz.
Require Import String.
Require Export Complex.
Require Import Quantum.
Require Import List.




(* Padding and lemmas *)
Definition pad {n} (start dim : nat) (A : Square (2^n)) : Square (2^dim) :=
  if start + n <=? dim then I (2^start) ⊗ A ⊗ I (2^(dim - (start + n))) else Zero.

Lemma WF_pad : forall n start dim (A : Square (2^n)),
  WF_Matrix A ->
  WF_Matrix (pad start dim A).
Proof.
  intros n start dim A WFA. unfold pad.
  bdestruct (start + n <=? dim); auto with wf_db.
Qed.  

Lemma pad_mult : forall n dim start (A B : Square (2^n)),
  pad start dim A × pad start dim B = pad start dim (A × B).
Proof.
  intros.
  unfold pad.
  gridify.
  reflexivity.
Qed.

Lemma pad_id : forall n dim,
  (n < dim)%nat -> @pad 1 n dim (I 2) = I (2 ^ dim).
Proof. intros. unfold pad. gridify. reflexivity. Qed.

Definition smpl_U (dim n : nat) (U : Square 2) : Square (2^dim) := @pad 1 n dim U.


Definition ctrl_U (dim m n: nat) (U: Square 2) :=
  if (m <? n) then
    @pad (1+(n-m-1)+1) m dim (∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ U .+ ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ I 2)
  else if (n <? m) then
    @pad (1+(m-n-1)+1) n dim (U ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣)
  else
    Zero.

(** some helper lemmas *)


(** Well-formedness **)

Lemma WF_smpl_U : forall dim n U, WF_Matrix U -> WF_Matrix (smpl_U dim n U).
Proof.
  intros. 
  unfold smpl_U.
  apply WF_pad; easy.
Qed.  

Lemma WF_ctrl_U : forall dim m n U, WF_Matrix U -> WF_Matrix (ctrl_U dim m n U).
  intros. 
  unfold ctrl_U.
  assert (H' : forall n, (2 * 2 ^ n * 2 = 2 ^ (1 + n + 1))%nat).
  { intros.
    do 2 rewrite Nat.pow_add_r, Nat.pow_1_r; easy. }
  bdestruct (m <? n); bdestruct (n <? m); try lia; auto with wf_db.
  all : apply WF_pad; rewrite H'; apply WF_plus; auto with wf_db.
Qed.  

#[global] Hint Resolve WF_pad WF_smpl_U WF_ctrl_U : wf_db.
