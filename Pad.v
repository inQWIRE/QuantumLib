Require Export Complex.
Require Export Quantum.
Require Export Init.Datatypes.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Lists.List.

(** This file provides padding functions to extend a matrix to a larger space.
   This is useful for describing the effect of 1- and 2-qubit gates on a larger
   quantum space. *)

Definition if_matrix {n} (b : bool) (u1 u2 : Square n) : Square n :=
  if b then u1 else u2.

Lemma WF_if_matrix : forall (n : nat) (b : bool) (u1 u2 : Square n), 
WF_Matrix u1 -> WF_Matrix u2 -> WF_Matrix (if_matrix b u1 u2).
Proof.
  intros. destruct b; assumption.
Qed.

Notation "A <| b |> B" := (if_matrix b A B) (at level 30).

Lemma if_matrix_mul : forall b n (A B C D : Square n),
    (A <|b|> B) × (C <| b |> D) = (A × C) <| b |> (B × D).
Proof.
  destruct b; reflexivity.
Qed.

(* converting this to if_matrix format results in WF_Matrix Zero not being solved by
auto with wf_db ?? *)
Definition pad2 {dim : nat} (A : Square 2) (i : nat) : Square (2^dim) :=
  if (i <? dim) then (I (2^i) ⊗ A ⊗ I (2^(dim - i - 1))) else Zero.

Lemma WF_pad2 : forall (i dim : nat) (A : Square 2),
WF_Matrix A -> WF_Matrix (@pad2 dim A i).
Proof.
  intros i dim A WF_A. unfold pad2.
  bdestruct_all; simpl; auto with wf_db.
Qed.

#[export] Hint Resolve WF_pad2 : wf_db.

Fixpoint embed2 {dim : nat} (lp : (list ((Square 2) * nat))) : Square (2^dim)  :=
  match lp with
  | (A, i) :: lp' => @Mmult (2^dim) (2^dim) (2^dim) (@pad2 dim A i) (embed2 lp')
  | _         => I (2^dim)
  end.

Lemma pad2_commutes : forall (A B : Square 2) (i j dim : nat),
i <> j ->
WF_Matrix A ->
WF_Matrix B ->
(i < dim)%nat -> 
(j < dim)%nat ->
@pad2 dim A i × @pad2 dim B j = @pad2 dim B j × @pad2 dim A i.
Proof.
  intros. unfold pad2.
  gridify; trivial.
  Qed.

Lemma WF_embed2 : forall (dim : nat) (lp : (list ((Square 2) * nat))),
Forall WF_Matrix (map fst lp) -> 
NoDup (map snd lp) ->
Forall (fun n => (n < dim)%nat) (map snd lp) ->
WF_Matrix (@embed2 dim lp).
intros. induction lp. 
+ unfold embed2; auto with wf_db.
+ destruct a. bdestruct (n <? dim); Msimpl; auto with wf_db.
  - inversion H; subst. inversion H0; subst. inversion H1; subst.
   simpl. apply WF_mult; auto with wf_db.
  - inversion H1; subst. lia.
Qed.

#[export] Hint Resolve WF_embed2 : wf_db.

Lemma embed2_commutes_base : forall (i j dim : nat)(A B : Square 2) 
(lp : (list ((Square 2) * nat))),
  i <> j ->
  WF_Matrix A ->
  WF_Matrix B ->
  (i < dim)%nat ->
  (j < dim)%nat ->
  @embed2 dim ((A, i) :: (B, j) :: lp) = @embed2 dim ((B, j) :: (A, i) :: lp).
  Proof.
    intros. simpl. rewrite <- Mmult_assoc. rewrite pad2_commutes; trivial.
    apply Mmult_assoc.
  Qed.

Lemma embed2_commutes : forall (dim : nat) (lp1 lp2 : list ((Square 2) * nat)),
  Forall WF_Matrix (map fst lp1) ->
  NoDup (map snd lp1) ->
  Forall (fun n => (n < dim)%nat) (map snd lp1) ->
  Permutation lp1 lp2 ->
  @embed2 dim lp1 = @embed2 dim lp2.
  Proof.
    intros. induction H2; trivial.
    + simpl. rewrite IHPermutation; trivial. 
      - simpl in *. inversion H; subst.
      auto.
      - inversion H0; auto.
      - simpl in H1. rewrite Forall_cons_iff in H1. apply H1.
    + destruct x, y. apply embed2_commutes_base.
      - simpl in H0. inversion H0; subst. simpl in *. intros n0eqn. apply H4. auto.
      - simpl in *. inversion H; subst.
      auto.
      - inversion H; subst. inversion H5; subst.
      auto.
      - inversion H1; auto.
      - inversion H1; subst. inversion H5; auto.
    + pose proof (Permutation_map snd H2_). rewrite IHPermutation1; 
    try rewrite IHPermutation2; trivial.
      - apply (Permutation_map fst) in H2_. eapply Permutation_Forall; eauto.
      - apply (Permutation_NoDup H2 H0).
      - eapply Permutation_Forall; eauto.
    Qed.

(* TODO: find function in stdlib *) 
Definition abs_diff (a b : nat) := Nat.max (a - b) (b - a).

Definition pad_ctrl (dim m n : nat) (u : Square 2) : Square (2^dim)%nat :=
  if m =? n then Zero
  else
    let b := m <? n in
    let μ := min m n in
    let δ := abs_diff m n in
    (@embed2 dim
    ([((∣1⟩⟨1∣ <|b|> u), μ)] ++
    [((u <|b|> ∣1⟩⟨1∣), (μ + δ)%nat)])) 
    .+ 
    (@embed2 dim
    ([((∣0⟩⟨0∣ <|b|> I 2), μ)] ++
    [((I 2 <|b|> ∣0⟩⟨0∣), (μ + δ)%nat)])).

Ltac rem_max_min :=
   unfold gt, ge, abs_diff in *;
  repeat match goal with 
  | [ H: (?a < ?b)%nat |- context[Init.Nat.max (?a - ?b) (?b - ?a)] ] => 
    rewrite (Max.max_r (a - b) (b - a)) by lia 
  | [ H: (?a < ?b)%nat |- context[Init.Nat.max (?b - ?a) (?a - ?b)] ] => 
    rewrite (Max.max_l (a - b) (b - a)) by lia 
  | [ H: (?a <= ?b)%nat |- context[Init.Nat.max (?a - ?b) (?b - ?a)] ] => 
    rewrite (Max.max_r (a - b) (b - a)) by lia 
  | [ H: (?a <= ?b)%nat |- context[Init.Nat.max (?b - ?a) (?a - ?b)] ] => 
    rewrite (Max.max_l (a - b) (b - a)) by lia   
  | [ H: (?a < ?b)%nat |- context[Init.Nat.min ?a ?b] ] => 
    rewrite Min.min_l by lia 
  | [ H: (?a < ?b)%nat |- context[Init.Nat.max ?a ?b] ] => 
    rewrite Max.max_r by lia 
  | [ H: (?a < ?b)%nat |- context[Init.Nat.min ?b ?a] ] => 
    rewrite Min.min_r by lia 
  | [ H: (?a < ?b)%nat |- context[Init.Nat.max ?b ?a] ] => 
    rewrite Max.max_l by lia 
  | [ H: (?a <= ?b)%nat |- context[Init.Nat.min ?a ?b] ] => 
    rewrite Min.min_l by lia 
  | [ H: (?a <= ?b)%nat |- context[Init.Nat.max ?a ?b] ] => 
    rewrite Max.max_r by lia 
  | [ H: (?a <= ?b)%nat |- context[Init.Nat.min ?b ?a] ] => 
    rewrite Min.min_r by lia 
  | [ H: (?a <= ?b)%nat |- context[Init.Nat.max ?b ?a] ] => 
    rewrite Max.max_l by lia 
  end.

Definition pad_u (dim n : nat) (u : Square 2) : Square (2^dim) := @pad2 dim u n.

(* also possible to define this in terms of pad directly *)
Definition pad_swap (dim m n: nat) :=
  pad_ctrl dim m n σx × pad_ctrl dim n m σx × pad_ctrl dim m n σx.

(** Well-formedness *)

Lemma WF_pad_u : forall dim n u, WF_Matrix u -> WF_Matrix (pad_u dim n u).
Proof.
  intros. 
  unfold pad_u.
  auto with wf_db. 
Qed.

Lemma WF_pad_ctrl : forall dim m n u, WF_Matrix u -> WF_Matrix (pad_ctrl dim m n u).
Proof.
  intros dim m n u WF_u.
  unfold pad_ctrl, abs_diff. bdestruct_all; simpl; rem_max_min;
  restore_dims; auto with wf_db.
  Qed.


Lemma WF_pad_swap : forall dim m n, WF_Matrix (pad_swap dim m n).
  intros.
  unfold pad_swap.
  repeat apply WF_mult; apply WF_pad_ctrl; apply WF_σx.
Qed.

#[export] Hint Resolve WF_pad2 WF_pad_u WF_pad_ctrl WF_if_matrix WF_pad_swap : wf_db.

(* Everything after here is a WIP wrt writing it in terms of embed2 *)

(** Unitarity *)
(* 
Lemma pad_unitary : forall n (u : Square (2^n)) i dim,
    (i < dim)%nat -> 
    WF_Unitary u ->
    WF_Unitary (@pad2 dim u i).
Proof.
  intros n u i dim lt_con [WF U_u].
  split.
  apply WF_pad2.
  apply WF.
  auto with wf_db.
  apply WF_pad2. apply WF.
  apply WF_pad; auto.
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

Lemma pad_ctrl'_unitary : forall dim m n u,
m <> n -> 
(m < dim)%nat ->
(n < dim)%nat ->
WF_Unitary u ->
WF_Unitary (pad_ctrl' dim m n u).
Proof.
  intros dim m n u neq_mn lm ln wfu.
  destruct wfu.
  unfold pad_ctrl', pad, WF_Unitary. bdestruct_all; simpl; try auto with wf_db.
  + replace (Init.Nat.min m n) with m in * by lia; split; restore_dims.
    - apply WF_kron; auto with wf_db.
    - Msimpl; unfold abs_diff;
    replace (Init.Nat.max (m - n) (n - m)) with ((n - m)%nat) by lia;
    gridify; rewrite H0; Qsimpl;
    replace (m + 1 + d + 1 + x - (m + S (d + 1)))%nat with x by lia;
    repeat rewrite kron_assoc; try auto with wf_db;
    repeat rewrite id_kron; restore_dims;
    rewrite <- kron_plus_distr_l; rewrite <- kron_plus_distr_r;
    rewrite Mplus10; repeat rewrite id_kron; reflexivity.
  + split; restore_dims.
    - auto with wf_db.
    - unfold abs_diff in H2; gridify.
  + replace (Init.Nat.min m n) with n by lia; unfold abs_diff;
  replace (Init.Nat.max (m - n)(n - m)) with (m - n)%nat by lia.
  split; restore_dims.
    - apply WF_kron; auto with wf_db.
    - Msimpl; gridify; Qsimpl; rewrite H0; 
    replace (n + 1 + x1 - n - 1)%nat with x1 by lia;
    repeat rewrite <- kron_assoc; try auto with wf_db;
    repeat rewrite id_kron; restore_dims;
    rewrite <- kron_plus_distr_r; rewrite <- kron_plus_distr_l;
    rewrite Mplus10; repeat rewrite id_kron;
    replace (n + 1 + (x1 + S x0) - (n + S (x1 + 1)))%nat with x0 by lia; reflexivity.
  + split; restore_dims.
  - auto with wf_db.
  - unfold abs_diff in H2; gridify.
  Qed.



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

(* theorems and lemmas about diagonalizability of matrices might be helpful
and make the next two proofs a lot faster.  *)

Lemma pad_A_ctrl'_commutes :  forall dim m n o A B,
m <> n ->
m <> o ->
WF_Matrix A ->
WF_Matrix B ->
pad_u dim m A × pad_ctrl' dim n o B = pad_ctrl' dim n o B × pad_u dim m A.
Proof.
  intros. unfold pad_ctrl', pad_u, pad, abs_diff.
  bdestruct_all; try auto with wf_db.
  - replace (Init.Nat.min n o) with n in * by lia.
  replace (Init.Nat.max (n - o) (o - n)) with (o - n)%nat in * by lia.
  replace (n + (1 + (o - n - 1) + 1))%nat with (o + 1)%nat in * by lia.
  simpl in *. 
  assert (WF_Diagonal (I (2 ^ m) ⊗ A ⊗ I (2 ^ (dim - (m + 1))))).
  + unfold WF_Diagonal. split. auto with wf_db.
  intros. gridify.
  Admitted.

Lemma pad_ctrl'_ctrl'_commutes : forall dim m n o p A B,
  m <> o ->
  m <> p ->
  n <> o ->
  n <> p ->
  WF_Matrix A ->
  WF_Matrix B ->
  pad_ctrl_embed dim m n A × pad_ctrl_embed dim o p B = pad_ctrl_embed dim o p B × pad_ctrl_embed dim m n A.
Proof.
  intros. unfold pad_ctrl_embed; bdestruct_all; rem_max_min; simpl;
  repeat rewrite le_plus_minus_r by lia; Msimpl; trivial. 




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
Qed. *)
