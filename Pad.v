Require Export Complex.
Require Export Quantum.
Require Export Eigenvectors.
Require Export Init.Datatypes.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Lists.List.

(** This file provides padding functions to extend a matrix to a larger space.
   This is useful for describing the effect of 1- and 2-qubit gates on a larger
   quantum space. *)

(* embed function such that commutativity follows directly from it
pad2 : padding square 2 matrices *)

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

(** Embedding matrices in I^dim *)


Definition pad2 {dim : nat} (A : Square 2) (i : nat) : Square (2^dim) :=
  I (2^i) ⊗ A ⊗ I (2^(dim - i - 1)).

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

Fixpoint embed2 {dim : nat} (lp : (list ((Square 2) * nat))) : Square (2^dim)  :=
  match lp with
  | (A, i) :: lp' => @Mmult (2^dim) (2^dim) (2^dim) (pad2 A i) (embed2 lp')
  | _         => I (2^dim)
  end.

(* Lemma pad2_diff_locations : forall (A B : Square 2) (i j : nat),
i <> j ->  *)

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

(* Inductive WF_Matrix_list {m n : nat} : (list (Matrix m n)) -> Prop :=
  | WF_nil :  WF_Matrix_list []
  | WF_cons (a : Matrix m n) (lA : (list (Matrix m n))) (H1 : WF_Matrix_list lA) (H2 : WF_Matrix a) : WF_Matrix_list (a :: lA). *)

Definition WF_Matrix_list {m n : nat} (la : list (Matrix m n)) : Prop 
:= forall  (a : Matrix m n),
In a la -> WF_Matrix a.


(* NoDup *)
(* Inductive disjoint_list {A : Type} : list A -> Prop :=
  | disjoint_nil : disjoint_list []
  | disjoint_succ (a : A) (lA : list A) (H1 : ~ In a lA) (H2 : disjoint_list lA) : disjoint_list (a :: lA). *)

Print Forall.
Check Permutation_Forall.

Lemma WF_list_permutation_WF : forall {m n : nat} (lp1 lp2 : list (Matrix m n)),
WF_Matrix_list lp2 -> Permutation lp1 lp2 -> WF_Matrix_list lp1.
Proof.
  intros. unfold WF_Matrix_list in *. intros.
  pose proof (Permutation_in a H0). apply H2 in H1. destruct H with a m n; trivial.
  left; lia. apply H; assumption.
  Qed. 
(*   
Lemma disjoint_list_permutation_disjoint : forall (A : Type) (l1 l2 : list A),
disjoint_list l1 -> Permutation l1 l2 -> disjoint_list l2.
Proof.
  intros. induction H0.
  + constructor.
  + apply disjoint_succ.
  (* x not in l, hence x not in l' *)
    - inversion H; subst.   *)

Lemma embed2_commutes : forall (dim : nat) (lp1 lp2 : list ((Square 2) * nat)),
  WF_Matrix_list (map fst lp1) ->
  NoDup (map snd lp1) ->
  Forall (fun n => (n < dim)%nat) (map snd lp1) ->
  Permutation lp1 lp2 ->
  @embed2 dim lp1 = @embed2 dim lp2.
  Proof.
    intros. induction H2; trivial.
    + simpl. rewrite IHPermutation; trivial. 
      - unfold WF_Matrix_list in H. simpl in *. destruct H with (fst x) 2%nat 2%nat.
      left. reflexivity. left. lia. unfold WF_Matrix_list.
      intros. apply H. right; assumption.
      - inversion H0; subst; assumption.
      - simpl in H1. rewrite Forall_cons_iff in H1. apply H1.
    + destruct x, y. apply embed2_commutes_base.
      - simpl in H0. inversion H0; subst. simpl in *. intros n0eqn.
      apply H4. left. symmetry. assumption.
      - unfold WF_Matrix_list in H. simpl in *. destruct H with m0 2%nat 2%nat.
      left. reflexivity. left. lia. specialize H with m0. apply H.
      left. reflexivity.
      - unfold WF_Matrix_list in H. simpl in *. destruct H with m 2%nat 2%nat.
      right. left. reflexivity. left. lia. specialize H with m. apply H.
      right. left. reflexivity.
      - inversion H1; subst. assumption.
      - inversion H1; subst. inversion H5; subst. assumption.
    + rewrite IHPermutation1. rewrite IHPermutation2.
    reflexivity.
    apply WF_list_permutation_WF with (map fst l); try assumption.
    apply Permutation_map, Permutation_sym. assumption.
    pose proof (Permutation_map snd H2_). apply (Permutation_NoDup H2 H0).
    pose proof (Permutation_map snd H2_). eapply Permutation_Forall. apply H2.
    all : assumption.
    Qed.
    
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

(* TODO: find actual function *) 
Definition abs_diff (a b : nat) := max (a - b) (b - a).
  
Definition pad_ctrl' (dim m n: nat) (u: Square 2) :=
  if m =? n then Zero
  else
    let b := m <? n in
    let μ := min m n in
    let δ := abs_diff m n in
    @pad (1 + (δ - 1) + 1) μ dim 
    ((∣1⟩⟨1∣ <|b|> u) ⊗ 
    I (2^(δ-1)) ⊗ (u <|b|> ∣1⟩⟨1∣) .+
                            (∣0⟩⟨0∣ <|b|> I 2) ⊗ 
                            I (2^(δ-1)) ⊗ (I 2 <|b|> ∣0⟩⟨0∣)).
       
(* TODO: find actual lemma *)
Lemma a_lt_b_abs_diff_a_b : forall (a b : nat),
(a < b)%nat -> ((a - b) < (b - a))%nat.
Proof.
  intros. lia.
  Qed.

Lemma lt_max : forall (a b : nat), 
(a < b)%nat -> (Init.Nat.max a b = b).
Proof.
  intros. lia.
  Qed.
                        
Lemma pad_ctrl_eq : forall dim m n u, pad_ctrl dim m n u = pad_ctrl' dim m n u.
Proof.
  intros. unfold pad_ctrl, pad_ctrl'. bdestruct_all; try easy.
  assert (Init.Nat.min m n = m). { lia. }
  all: unfold abs_diff; simpl.
  rewrite H1; apply a_lt_b_abs_diff_a_b in H; apply lt_max in H; 
  rewrite H; trivial.
  assert (Init.Nat.min m n = n). { lia. }
  rewrite H2. apply a_lt_b_abs_diff_a_b in H0; 
  apply lt_max in H0. 
  assert (Init.Nat.max (n - m) (m - n) = Init.Nat.max (m - n) (n - m)). { lia. }
  rewrite H3 in H0. rewrite H0. trivial.
  Qed.



    
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

Search Init.Nat.min (_ <= _)%nat.

Lemma WF_pad_ctrl' : forall dim m n u, WF_Matrix u -> WF_Matrix (pad_ctrl' dim m n u).
Proof.
  intros. unfold pad_ctrl'. bdestruct_all; try easy.
  - simpl; replace (Init.Nat.min m n) with m by lia. 
  apply WF_pad; restore_dims; auto with wf_db.
  - simpl; replace (Init.Nat.min m n) with n by lia. 
  apply WF_pad; restore_dims; auto with wf_db.
  Qed.

Lemma WF_pad_swap : forall dim m n, WF_Matrix (pad_swap dim m n).
  intros.
  unfold pad_swap.
  repeat apply WF_mult; apply WF_pad_ctrl; apply WF_σx.
Qed.

#[export] Hint Resolve WF_pad WF_pad_u WF_pad_ctrl WF_pad_ctrl' WF_if_matrix WF_pad_swap : wf_db.

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
  pad_ctrl' dim m n A × pad_ctrl' dim o p B = pad_ctrl' dim o p B × pad_ctrl' dim m n A.
Proof.
  intros. unfold pad_ctrl', pad, abs_diff.
  repeat match goal with
  | |- context [if_matrix ?b ?A ?B] => let M := fresh "M" in
  remember (if_matrix b A B) as M end.
  bdestruct_all; Msimpl_light; trivial.
  gridify.
  
  bdestruct_all; simpl; 
  try auto with wf_db.
  + replace (Init.Nat.min m n) with m in * by lia.
    replace (Init.Nat.min o p) with o in * by lia.
    replace (Init.Nat.max (m - n) (n - m)) with (n - m)%nat in * by lia.
    replace (Init.Nat.max (o - p) (p - o)) with (p - o)%nat in * by lia.
    Admitted.





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
