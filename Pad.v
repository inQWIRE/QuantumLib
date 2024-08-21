Require Export Complex.
Require Export Quantum.
Require Export Init.Datatypes.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Lists.List.
(** This file provides padding functions to extend a matrix to a larger space.
   This is useful for describing the effect of 1- and 2-qubit gates on a larger
   quantum space. *)

(* if_matrix notation + lemmas *)

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

#[export] Hint Resolve WF_if_matrix : wf_db.

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

(* pad2x2, embed definition + lemmas about commutation *)
Definition pad2x2 {dim : nat} (A : Square 2) (i : nat) : Square (2^dim) :=
  if (i <? dim) then (I (2^i) ⊗ A ⊗ I (2^(dim - i - 1))) else Zero.

Lemma WF_pad2x2 : forall (i dim : nat) (A : Square 2),
WF_Matrix A -> WF_Matrix (@pad2x2 dim A i).
Proof.
  intros i dim A WF_A. unfold pad2x2.
  bdestruct_all; simpl; auto with wf_db.
Qed.

#[export] Hint Resolve WF_pad2x2 : wf_db.

Fixpoint embed {dim : nat} (lp : (list ((Square 2) * nat))) : Square (2^dim)  :=
  match lp with
  | (A, i) :: lp' => @Mmult (2^dim) (2^dim) (2^dim) (@pad2x2 dim A i) (embed lp')
  | _         => I (2^dim)
  end.


Lemma pad2x2_commutes : forall (A B : Square 2) (i j dim : nat),
i <> j ->
WF_Matrix A ->
WF_Matrix B ->
@pad2x2 dim A i × @pad2x2 dim B j = @pad2x2 dim B j × @pad2x2 dim A i.
Proof.
  intros. unfold pad2x2.
  gridify; trivial.
  Qed.

Lemma WF_embed : forall (dim : nat) (lp : (list ((Square 2) * nat))),
Forall WF_Matrix (map fst lp) -> 
NoDup (map snd lp) ->
Forall (fun n => (n < dim)%nat) (map snd lp) ->
WF_Matrix (@embed dim lp).
intros. induction lp. 
+ unfold embed; auto with wf_db.
+ destruct a. bdestruct (n <? dim); Msimpl; auto with wf_db.
  - inversion H; subst. inversion H0; subst. inversion H1; subst.
   simpl. apply WF_mult; auto with wf_db.
  - inversion H1; subst. lia.
Qed.

#[export] Hint Resolve WF_embed : wf_db.

Lemma embed_commutes_base : forall (i j dim : nat)(A B : Square 2) 
(lp : (list ((Square 2) * nat))),
  i <> j ->
  WF_Matrix A ->
  WF_Matrix B ->
  (i < dim)%nat ->
  (j < dim)%nat ->
  @embed dim ((A, i) :: (B, j) :: lp) = @embed dim ((B, j) :: (A, i) :: lp).
  Proof.
    intros. simpl. rewrite <- Mmult_assoc. rewrite pad2x2_commutes; trivial.
    apply Mmult_assoc.
  Qed.

Lemma embed_commutes : forall (dim : nat) (lp1 lp2 : list ((Square 2) * nat)),
  Forall WF_Matrix (map fst lp1) ->
  NoDup (map snd lp1) ->
  Forall (fun n => (n < dim)%nat) (map snd lp1) ->
  Permutation lp1 lp2 ->
  @embed dim lp1 = @embed dim lp2.
  Proof.
    intros. induction H2; trivial.
    + simpl. rewrite IHPermutation; trivial. 
      - simpl in *. inversion H; subst.
      auto.
      - inversion H0; auto.
      - simpl in H1. 
        apply Forall_inv_tail in H1.
        assumption.
    + destruct x, y. apply embed_commutes_base.
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

Lemma embed_mult : forall (dim : nat) (lp1 lp2 : list ((Square 2) * nat)),
Forall WF_Matrix (map fst lp1) ->
Forall WF_Matrix (map fst lp2) ->
NoDup (map snd lp1) ->
NoDup (map snd lp2) ->
Forall (fun n : nat => (n < dim)%nat) (map snd lp1) ->
Forall (fun n : nat => (n < dim)%nat) (map snd lp2) ->
@embed dim lp1 × @embed dim lp2 = @embed dim (lp1 ++ lp2).
Proof.
  intros. induction lp1.
  + simpl. apply Mmult_1_l. apply WF_embed; trivial.
  + simpl. rewrite <- IHlp1. destruct a. apply Mmult_assoc.
  inversion H; auto.
  inversion H1; auto.
  inversion H3; auto.
Qed.

(* TODO: find function in stdlib *) 
Definition abs_diff (a b : nat) := Nat.max (a - b) (b - a).

Definition pad2x2_ctrl (dim m n : nat) (u : Square 2) : Square (2^dim)%nat :=
  if m =? n then Zero
  else
    let b := m <? n in
    let μ := min m n in
    let δ := abs_diff m n in
    (@embed dim
    ([((∣1⟩⟨1∣ <|b|> u), μ)] ++
    [((u <|b|> ∣1⟩⟨1∣), (μ + δ)%nat)])) 
    .+ 
    (@embed dim
    ([((∣0⟩⟨0∣ <|b|> I 2), μ)] ++
    [((I 2 <|b|> ∣0⟩⟨0∣), (μ + δ)%nat)])).

Ltac rem_max_min :=
   unfold gt, ge, abs_diff in *;
  repeat match goal with 
  | [ H: (?a < ?b)%nat |- context[Nat.max (?a - ?b) (?b - ?a)] ] => 
    rewrite (Nat.max_r (a - b) (b - a)) by lia 
  | [ H: (?a < ?b)%nat |- context[Nat.max (?b - ?a) (?a - ?b)] ] => 
    rewrite (Nat.max_l (b - a) (a - b)) by lia 
  | [ H: (?a <= ?b)%nat |- context[Nat.max (?a - ?b) (?b - ?a)] ] => 
    rewrite (Nat.max_r (a - b) (b - a)) by lia 
  | [ H: (?a <= ?b)%nat |- context[Nat.max (?b - ?a) (?a - ?b)] ] => 
    rewrite (Nat.max_l (b - a) (a - b)) by lia   
  | [ H: (?a < ?b)%nat |- context[Nat.min ?a ?b] ] => 
    rewrite Nat.min_l by lia 
  | [ H: (?a < ?b)%nat |- context[Nat.max ?a ?b] ] => 
    rewrite Nat.max_r by lia 
  | [ H: (?a < ?b)%nat |- context[Nat.min ?b ?a] ] => 
    rewrite Nat.min_r by lia 
  | [ H: (?a < ?b)%nat |- context[Nat.max ?b ?a] ] => 
    rewrite Nat.max_l by lia 
  | [ H: (?a <= ?b)%nat |- context[Nat.min ?a ?b] ] => 
    rewrite Nat.min_l by lia 
  | [ H: (?a <= ?b)%nat |- context[Nat.max ?a ?b] ] => 
    rewrite Nat.max_r by lia 
  | [ H: (?a <= ?b)%nat |- context[Nat.min ?b ?a] ] => 
    rewrite Nat.min_r by lia 
  | [ H: (?a <= ?b)%nat |- context[Nat.max ?b ?a] ] => 
    rewrite Nat.max_l by lia 
  end.

Definition pad2x2_u (dim n : nat) (u : Square 2) : Square (2^dim) := @embed dim [(u,n)].

(* also possible to define this in terms of pad2x2 directly *)
Definition pad2x2_swap (dim m n: nat) :=
  pad2x2_ctrl dim m n σx × pad2x2_ctrl dim n m σx × pad2x2_ctrl dim m n σx.

(** Well-formedness *)

Lemma WF_pad2x2_u : forall dim n u, WF_Matrix u -> WF_Matrix (pad2x2_u dim n u).
Proof.
  intros. 
  unfold pad2x2_u.
  unfold embed.
  auto with wf_db. 
Qed.

Lemma WF_pad2x2_ctrl : forall dim m n u, WF_Matrix u -> WF_Matrix (pad2x2_ctrl dim m n u).
Proof.
  intros dim m n u WF_u.
  unfold pad2x2_ctrl, abs_diff. bdestruct_all; simpl; rem_max_min;
  restore_dims; auto with wf_db.
  Qed.


Lemma WF_pad2x2_swap : forall dim m n, WF_Matrix (pad2x2_swap dim m n).
  intros.
  unfold pad2x2_swap.
  repeat apply WF_mult; apply WF_pad2x2_ctrl; apply WF_σx.
Qed.

#[export] Hint Resolve WF_pad2x2 WF_pad2x2_u WF_pad2x2_ctrl WF_pad2x2_swap : wf_db.

(* tactics for NoDup *)
Ltac NoDupity :=
  repeat match goal with
  | |- NoDup [?a] => repeat constructor; auto
  | |- NoDup _=> repeat constructor; intros []; try lia; auto
  | [ H1: In ?a ?b |- False ] => inversion H1; auto
  end.

(* Lemmas about commutativity *)

Lemma pad2x2_A_B_commutes : forall dim m n A B,
  m <> n ->
  (m < dim)%nat ->
  (n < dim)%nat ->
  WF_Matrix A ->
  WF_Matrix B ->
  pad2x2_u dim m A × pad2x2_u dim n B = pad2x2_u dim n B × pad2x2_u dim m A.
Proof.
  intros. unfold pad2x2_u. unfold WF_Matrix in *.
  repeat rewrite embed_mult. apply embed_commutes.
  all : simpl; try auto with wf_db; NoDupity.
  constructor.
Qed.


Ltac comm_pad2x2 :=
  repeat match goal with
  | |- context[?A = ?B] => match A with
      | context[@pad2x2 ?dim ?X ?x × @pad2x2 ?dim ?Y ?y × @pad2x2 ?dim ?Z ?z] =>
      match B with
        | context[pad2x2 Z z × pad2x2 X x × pad2x2 Y y] =>
          try rewrite (pad2x2_commutes Z X z x dim); 
          try rewrite <- (Mmult_assoc (pad2x2 X x) (pad2x2 Z z) (pad2x2 Y y));
          try rewrite (pad2x2_commutes Y Z y z dim)
        | context[pad2x2 Y y × pad2x2 Z z × pad2x2 X x] =>
          try rewrite (Mmult_assoc (pad2x2 Y y) (pad2x2 Z z) (pad2x2 X x));
          try rewrite (pad2x2_commutes Z X z x dim);
          try rewrite <- (Mmult_assoc (pad2x2 Y y) (pad2x2 X x) (pad2x2 Z z));
          try rewrite (pad2x2_commutes Y X y x dim)
        end
      | context[@pad2x2 ?dim ?X ?x × (@pad2x2 ?dim ?Y ?y × @pad2x2 ?dim ?Z ?z)] => 
        rewrite <- (Mmult_assoc (pad2x2 X x) (pad2x2 Y y) (pad2x2 Z z))
      end
    end.


Lemma pad2x2_A_ctrl_commutes : forall dim m n o A B,
  m <> n ->
  m <> o ->
  (m < dim)%nat ->
  (n < dim)%nat ->
  (o < dim)%nat ->
  WF_Matrix A ->
  WF_Matrix B ->
  pad2x2_u dim m A × pad2x2_ctrl dim n o B = pad2x2_ctrl dim n o B × pad2x2_u dim m A.
Proof.
  Opaque embed.
  intros. unfold pad2x2_u, pad2x2_ctrl, abs_diff. bdestruct_all; simpl; rem_max_min;
  Msimpl; trivial.
  + repeat rewrite Mmult_plus_distr_l; repeat rewrite Mmult_plus_distr_r.
  rewrite le_plus_minus_r' by (apply Nat.lt_le_incl; trivial).
  repeat rewrite embed_mult; simpl.
  rewrite (embed_commutes dim [(A, m); (∣1⟩⟨1∣, n); (B, o)] [(∣1⟩⟨1∣, n); (B, o); (A, m)]).
  rewrite (embed_commutes dim [(A, m); (∣0⟩⟨0∣, n); (I 2, o)] [(∣0⟩⟨0∣, n); (I 2, o); (A, m)]).
  trivial.
  all : simpl; NoDupity; auto with wf_db. 
  all : rewrite perm_swap; apply perm_skip; apply perm_swap.

  + repeat rewrite Mmult_plus_distr_l; repeat rewrite Mmult_plus_distr_r.
  rewrite le_plus_minus_r' by trivial; repeat rewrite embed_mult; simpl.
  rewrite (embed_commutes dim [(A, m); (B, o); (∣1⟩⟨1∣, n)] [(B, o); (∣1⟩⟨1∣, n); (A, m)]).
  rewrite (embed_commutes dim [(A, m); (I 2, o); (∣0⟩⟨0∣, n)] [(I 2, o); (∣0⟩⟨0∣, n); (A, m)]).
  trivial.
  all : simpl; NoDupity; auto with wf_db.
  all : rewrite perm_swap; apply perm_skip; apply perm_swap.
Qed.

(** Unitarity *)

Lemma pad_unitary : forall n (u : Square (2^n)) start dim,
    (start + n <= dim)%nat -> 
    WF_Unitary u ->
    WF_Unitary (pad start dim u).
Proof.
  intros n u start dim B [WF U].
  split. apply WF_pad; auto.
  unfold pad.
  Modulus.bdestructΩ'.
  Msimpl.
  rewrite U.
  rewrite 2!id_kron.
  f_equal.
  unify_pows_two.
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

Lemma pad_u_mmult : forall dim b A B, WF_Matrix A -> WF_Matrix B ->
  pad_u dim b (A × B) = pad_u dim b A × pad_u dim b B.
Proof.
  intros.
  unfold pad_u, pad.
  bdestruct_all; now Msimpl.
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
(*
  bdestruct_all; try lia. 
  all : repeat rewrite Mmult_0_l; repeat rewrite Mmult_0_r; auto.
  prep_matrix_equality.
  unfold Mmult.
  unfold kron.
  apply mat_equiv_eq. apply WF_mult.
*)
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
  all: gridify; trivial.
Qed.
