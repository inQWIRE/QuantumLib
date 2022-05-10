Require Export Complex.
Require Export Quantum.

(** This file provides padding functions to extend a matrix to a larger space.
   This is useful for describing the effect of 1- and 2-qubit gates on a larger
   quantum space. *)

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

Definition pad_u (dim n : nat) (u : Square 2) : Square (2^dim) := @pad 1 n dim u.

Definition pad_ctrl (dim m n: nat) (u: Square 2) :=
  if (m <? n) then
    @pad (1+(n-m-1)+1) m dim (∣1⟩⟨1∣ ⊗ I (2^(n-m-1)) ⊗ u .+ ∣0⟩⟨0∣ ⊗ I (2^(n-m-1)) ⊗ I 2)
  else if (n <? m) then
    @pad (1+(m-n-1)+1) n dim (u ⊗ I (2^(m-n-1)) ⊗ ∣1⟩⟨1∣ .+ I 2 ⊗ I (2^(m-n-1)) ⊗ ∣0⟩⟨0∣)
  else
    Zero.

(* also possible to define this in terms of pad directly *)
Definition pad_swap (dim m n: nat) :=
  pad_ctrl dim m n σx × pad_ctrl dim n m σx × pad_ctrl dim m n σx.

(** Well-formedness *)

Lemma WF_pad_u : forall dim n u, WF_Matrix u -> WF_Matrix (pad_u dim n u).
Proof.
  intros. 
  unfold pad_u.
  apply WF_pad; easy.
Qed.

Lemma WF_pad_ctrl : forall dim m n u, WF_Matrix u -> WF_Matrix (pad_ctrl dim m n u).
  intros. 
  unfold pad_ctrl.
  assert (H' : forall n, (2 * 2 ^ n * 2 = 2 ^ (1 + n + 1))%nat).
  { intros.
    do 2 rewrite Nat.pow_add_r, Nat.pow_1_r; easy. }
  bdestruct (m <? n); bdestruct (n <? m); try lia; auto with wf_db.
  all : apply WF_pad; rewrite H'; apply WF_plus; auto with wf_db.
Qed.

Lemma WF_pad_swap : forall dim m n, WF_Matrix (pad_swap dim m n).
  intros.
  unfold pad_swap.
  repeat apply WF_mult; apply WF_pad_ctrl; apply WF_σx.
Qed.

#[export] Hint Resolve WF_pad WF_pad_u WF_pad_ctrl WF_pad_swap : wf_db.

(** Unitarity *)

Lemma pad_unitary : forall n (u : Square (2^n)) start dim,
    (start + n <= dim)%nat -> 
    WF_Unitary u ->
    WF_Unitary (pad start dim u).
Proof.
  intros n u start dim B [WF U].
  split. apply WF_pad; auto.
  unfold pad.
  gridify.
  Msimpl.
  rewrite U.
  reflexivity.
Qed.

Lemma pad_u_unitary : forall dim n u,
    (n < dim)%nat ->
    WF_Unitary u ->
    WF_Unitary (pad_u dim n u).
Proof. intros. apply pad_unitary. lia. auto. Qed.  

Lemma pad_ctrl_unitary : forall dim m n u,
    m <> n ->
    (m < dim)%nat ->
    (n < dim)%nat ->
    WF_Unitary u ->
    WF_Unitary (pad_ctrl dim m n u).
Proof.
  intros dim m n u NE Lm Ln WFU.
  unfold pad_ctrl, pad.
  destruct WFU as [WF U].
  gridify.
  - split.
    + apply WF_plus; auto with wf_db.
    + Qsimpl.
      gridify.
      rewrite U.
      Qsimpl.
      repeat rewrite <- kron_plus_distr_r.
      repeat rewrite <- kron_plus_distr_l.
      Qsimpl.
      reflexivity.
  - split.
    + apply WF_plus; auto with wf_db.
    + Msimpl.
      gridify.
      rewrite U.
      Qsimpl.
      repeat rewrite <- kron_plus_distr_r.
      repeat rewrite <- kron_plus_distr_l.
      Qsimpl.
      reflexivity.
Qed.

Lemma pad_swap_unitary : forall dim m n,
    m <> n ->
    (m < dim)%nat ->
    (n < dim)%nat ->
    WF_Unitary (pad_swap dim m n).
Proof. 
  intros. 
  repeat apply Mmult_unitary;
    apply pad_ctrl_unitary; auto; apply σx_unitary. 
Qed.

(** Lemmas about commutation *)

Lemma pad_A_B_commutes : forall dim m n A B,
  m <> n ->
  WF_Matrix A ->
  WF_Matrix B ->
  pad_u dim m A × pad_u dim n B = pad_u dim n B × pad_u dim m A.
Proof.
  intros.
  unfold pad_u, pad.
  gridify; trivial.
Qed.

(* A bit slow, due to six valid subcases *)
Lemma pad_A_ctrl_commutes : forall dim m n o A B,
  m <> n ->
  m <> o ->
  WF_Matrix A ->
  WF_Matrix B ->
  pad_u dim m A × pad_ctrl dim n o B = pad_ctrl dim n o B × pad_u dim m A.
Proof.
  intros.
  unfold pad_ctrl, pad_u, pad.
  gridify; trivial.
Qed.

(* Horribly slow due to many subcases.
   TODO: can we speed this up be tweaking the ordering in gridify? *)
Lemma pad_ctrl_ctrl_commutes : forall dim m n o p A B,
  m <> o ->
  m <> p ->
  n <> o ->
  n <> p ->
  WF_Matrix A ->
  WF_Matrix B ->
  pad_ctrl dim m n A × pad_ctrl dim o p B = pad_ctrl dim o p B × pad_ctrl dim m n A.
Proof.
  intros.
  unfold pad_ctrl, pad.
  bdestruct_all.
  all : try rewrite Mmult_0_r; try rewrite Mmult_0_l; try easy.
  

Admitted.
  (* gridify; trivial. *)
(*Qed.*)
